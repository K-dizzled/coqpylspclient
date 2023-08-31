import progressbar
from typing import Callable

class ProgressBar:
    def __init__(
        self, 
        on_update: Callable[[int], None], 
        on_init: Callable[[int], None], 
        on_end: Callable[[], None]
    ) -> None:
        self.current = None
        self.total = None
        self.on_update = on_update
        self.on_init = on_init
        self.on_end = on_end
    
    def initialize(self, total: int) -> None:
        self.current = 0
        self.total = total
        self.on_init(self.total)

    def update_count(self, new_count: int) -> None:
        self.on_update(new_count)
        if self.total is None or self.current is None:
            raise Exception("Progress bar is not initialized")
        self.current = new_count
    
    def increase_count(self) -> None:
        self.on_update(self.current)
        if self.total is None or self.current is None:
            raise Exception("Progress bar is not initialized")
        self.current += 1
    
    def finish(self) -> None:
        if self.total is None or self.current is None:
            raise Exception("Progress bar is not initialized")
        self.on_end()


class AliveProgressBar(ProgressBar): 
    def __on_init(self, total: int) -> None:
        widgets = [
            'Processing: ', progressbar.Percentage(),
            ' ', progressbar.Bar(marker='*', left='[', right=']'),
            ' ', progressbar.Timer(),
            ' ', progressbar.ETA()
        ]
        self.total = total
        self.bar = progressbar.ProgressBar(widgets=widgets, maxval=total).start()

    def __on_update_count(self, new_count: int) -> None:
        self.bar.update(new_count)

    def __on_end(self) -> None:
        self.bar.update(self.total)
        self.bar.finish()

    def __init__(self) -> None:
        super().__init__(self.__on_update_count, self.__on_init, self.__on_end)

    
class StdoutProgressBar(ProgressBar): 
    def __on_init(self, total: int) -> None:
        self.last_updated = 0
        print(f"{self.sys_msg_start} {total}")

    def __on_update_count(self, new_count: int) -> None:
        prev_percent = (self.last_updated * 100) // self.total
        new_percent = (new_count * 100) // self.total
        if new_percent - prev_percent >= self.log_every_n_percent:
            print(f"{self.sys_update_msg_prefix} {new_count}")
            self.last_updated = new_count

    def __on_end(self) -> None:
        print(f"{self.sys_msg_end}")

    def __init__(
        self, 
        sys_msg_start: str,
        sys_msg_end: str,
        sys_update_msg_prefix: str,
        log_every_n_percent: int = 10
    ) -> None:
        self.sys_msg_start = sys_msg_start
        self.sys_msg_end = sys_msg_end
        self.sys_update_msg_prefix = sys_update_msg_prefix
        self.log_every_n_percent = log_every_n_percent
        super().__init__(self.__on_update_count, self.__on_init, self.__on_end)