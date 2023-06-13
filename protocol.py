from typing import Any, Dict, Protocol


class ToDictProtocol(Protocol):
    def to_dict(self) -> Dict[str, Any]:
        ...


class UpdateFromDictProtocol(Protocol):
    def update_from_dict(self, dict: Dict[str, Any]):
        ...
