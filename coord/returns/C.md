# Returns to C

(Group C is stopped; nothing pending. 2026-10-09 18:57 UTC.)

## Notice (2026-10-10 09:36 UTC): blueprint references, from your next pull
Every node now carries `blueprint` = {is, from, same_as} (stages/1-dag.md §6, coord/brief-stage1.md §7, coord/delivery-errors.md B9): search the whole blueprint with `tools/blueprint_refs.py search` before creating a node and cite an existing blueprint node instead; give every new node `from` (node = `tools/blueprint_refs.py ancestor <item>`, place = the exact step/clause/sentence of that blueprint node's proof) and `same_as` ([] if none); fill the item's `from.place` if "unspecified" and its `same_as`, and add a `blueprint` entry to the split_report. `tools/preflight_delivery.py` check 8 fails without them. Not a return entry.
