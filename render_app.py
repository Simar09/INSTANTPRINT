import logging
from pathlib import Path
from app import LocalPrintServer, SessionManager, PrinterInfo

# 1. Setup Mock Logger
logger = logging.getLogger("RenderMock")
logger.setLevel(logging.INFO)
handler = logging.StreamHandler()
logger.addHandler(handler)

# 2. Mock the Windows-only PrinterManager
class MockPrinterManager:
    def __init__(self, logger):
        self.logger = logger
    def enumerate_printers(self):
        return [PrinterInfo(
            name="Render Cloud Printer", driver="Mock", port="Cloud", 
            connection="Cloud", status="Ready", status_bits=0, 
            jobs=0, is_default=True, available=True
        )]
    def inspect_printer(self, name):
        return self.enumerate_printers()[0]
    def get_capabilities(self, info):
        return {"duplex": True, "papers": []}
    def job_state(self, printer_name, job_id):
        return "Printed"
    def shutdown(self):
        pass

# 3. Mock the PrintManager so it simulates printing instead of crashing
class MockPrintManager:
    def __init__(self, logger, sessions, printers, temp_root):
        self.sessions = sessions
    def submit(self, token, path, extension, kind, options):
        # Simulate a successful print job
        self.sessions.update(token, "printing", "Simulating print on Render...")
        self.sessions.finish(token, True, "Print simulated successfully on Render cloud.")
    def shutdown(self):
        pass

# 4. Override the Local Network Guard (so you can access it over the public internet)
class CloudPrintServer(LocalPrintServer):
    def _allowed_client(self) -> bool:
        return True  # Bypass the LAN-only check for Render

# 5. Initialize the server
sessions = SessionManager(logger, lambda: 3600)  # 1 hour sessions
temp_root = Path("/tmp")
temp_root.mkdir(exist_ok=True)
printers = MockPrinterManager(logger)
print_manager = MockPrintManager(logger, sessions, printers, temp_root)

server = CloudPrintServer(
    sessions=sessions,
    print_manager=print_manager,
    temp_root=temp_root,
    max_upload=lambda: 100 * 1024 * 1024,
    logger=logger
)

# 6. Generate a permanent test session token for Render
dummy_printer = printers.enumerate_printers()[0]
session = sessions.create(dummy_printer, printers.get_capabilities(dummy_printer))
logger.info(f"*** TEST URL FOR RENDER: /s/{session.token} ***")

# Expose the Flask app for Gunicorn
app = server.flask
