# Returns to E

(Group E is stopped; nothing pending. 2026-10-09 18:57 UTC.)

## Notice (2026-10-10 09:36 UTC): blueprint references, from your next pull
Every node now carries `blueprint` = {is, from, same_as} (stages/1-dag.md §6, coord/brief-stage1.md §7, coord/delivery-errors.md B9): search the whole blueprint with `tools/blueprint_refs.py search` before creating a node and cite an existing blueprint node instead; give every new node `from` (node = `tools/blueprint_refs.py ancestor <item>`, place = the exact step/clause/sentence of that blueprint node's proof) and `same_as` ([] if none); fill the item's `from.place` if "unspecified" and its `same_as`, and add a `blueprint` entry to the split_report. `tools/preflight_delivery.py` check 8 fails without them. Not a return entry.

**Notice (2026-10-10 12:45 UTC): fields of a node, sandbox, preflight check 9.** Decision of the human (this evening): one clone per group, read-only for workers, a sandbox `/home/ubuntu/weil-sandbox/<group>/<item>/` per item, the lead packages each delivery in the clone taking every existing node file as it is on `origin/sheaf-dag` and setting only the fields a split owns (`roles/remote-lead.md` §2, §4). The list of those fields is `tools/README.md` "Fields of a node: who sets them" (`tools/node_fields.py`); `tools/preflight_delivery.py` now has check 9: the maintainer's fields of the item (`lean_audit`, `lean`, `blueprint.is`, `created`, `reviewed`, `lead_note`, `tool_uses`, `import_flags`, ...) unchanged against the base, and no such field on a new node (`blueprint.is` null). Pull before your next preflight. Not a return entry.

*(13:34 UTC) Notice: the preflight no longer reads `[n-1]`, `[m]` as node citations (a node id has at least two hyphens); no need to escape brackets in formulas. Pull. Not a return entry.*

*(2026-10-10 13:58 UTC) Notice: several reports today say the Stacks TeX or the blueprint files are missing on your machine and file WANTED lines; both are in the repository (`literature/stacks-project/*.tex` with `tags/tags`, `literature/blueprint/master/blueprint/`; rebuild with `tools/fetch_literature.sh` if your clone lacks them). A WANTED for a file that is in the repository is not acted on; read the source before delivering. Not a return entry.*
