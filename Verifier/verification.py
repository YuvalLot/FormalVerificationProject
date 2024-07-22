

class Verification:
    
    def __init__(self, success: bool, msg: str) -> None:
        self.success = success
        self.msg = msg

    def __str__(self) -> str:
        if self.success:
            return f"Successfuly Verified."
        else:
            return f"Verification Error: {self.msg}."