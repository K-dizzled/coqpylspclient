from .coq_lsp_client import CoqLspClient
from .coq_lsp_structs import *
from pylspclient.lsp_structs import *
from typing import Tuple
from pathlib import Path
import os
import uuid

# Not used now
class AuxUtils(object): 
    def  __init__(self, lib_file_path: str) -> None: 
        self.lib_file_path = lib_file_path
        self.abs_file_path = os.path.abspath(lib_file_path)
        self.abs_uri = f"file://{self.abs_file_path}"
        path_to_coq_file = Path(lib_file_path)
        parent_dir = path_to_coq_file.parent.absolute()
        self.parent_dir_uri = f"file://{parent_dir}"
    
    def __save_vo(self) -> None:
        client = CoqLspClient(self.parent_dir_uri)
        with open(self.abs_file_path, 'r') as f:
            client.didOpen(TextDocumentItem(self.abs_uri, 'coq', 1, f.read()))
        versionId = VersionedTextDocumentIdentifier(self.abs_uri, 1)
        client.save_vo(versionId)
        client.shutdown()
        client.exit()

    def __get_import_text(self, package_name: str) -> str: 
        return f"Require Import {package_name}."