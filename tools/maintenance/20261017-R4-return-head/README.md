# R4 return-head parser repair, 2026-10-17

`tools/batch_land.py` wrote return headers with `head SHA`, while the unified
launcher parsed only `branch head SHA`. R4's rejected head was `8ad217867`.
After R4 pushed the replacement `885035f293`, the launcher still read an empty
head and dispatched repeated repairs instead of leaving that delivery for review.
The last ten failed attempts ended with provider HTTP 429 errors; empty final
answer files concealed that diagnosis behind `NOANSWER:`.

The producer now writes the same `branch head SHA` format as
`tools/merge_delivery.py`. The launcher repair accepts both formats, so historical
batch returns remain usable, and retains fatal log diagnostics for empty answers.
No historical failure count gates dispatch. A rejected current head still retries
at 10,000 failures; a replacement head waits for its existing review flow.

`patch_dispatcher.py` is the scoped launcher change, archived here because the
launcher directory is not a Git repository. It does not replace unrelated source
or import the dispatcher. Install with:

```sh
python3 patch_dispatcher.py /home/ubuntu/weil-launcher-all/dispatch_all.py
DISPATCH_SOURCE=/home/ubuntu/weil-launcher-all/dispatch_all.py \
  python3 test_dispatch_return_records.py -v
```

The installer keeps a `.bak` before an actual edit and is idempotent. The launcher
source was installed in place during maintenance. The running dispatcher is not
restarted by this patch; no process owned by another session may be killed.
Future batch returns already use the canonical format understood by the old
running dispatcher. Existing R4 return retirement occurred through normal landing.

During maintenance another pipeline repair added provider-capacity admission and
batch-specific group-state handling to the launcher. This patch preserves those
changes. It does not claim to resolve the external provider's service capacity.
