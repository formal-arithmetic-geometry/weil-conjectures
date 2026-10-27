# Q34 presheaf bar ownership maintenance, 2026-10-25

Return H2 at cc2cf7441226 requested extraction of the definitions from the
existence-theorem module. Q34 correctly performed that extraction, but replacing
the theorem statement dependency by its definition owner put the required theorem
module/record edit outside the prerequisite closure. The preflight then discarded
the record and reported its module as unowned; repeated dispatch could not fix it.

This maintenance lands the shared-library extraction separately. All 26 definitions
and structure fields are byte-identical modulo blueprint tags to the existing,
independently reviewed module. exists_resolution and its full proof docstring are
byte-identical. PresheafBarResolution publicly imports PresheafBarResolutionData,
preserving existing importers and declaration names. The existence node records
its definition prerequisite and owns only exists_resolution. The definition node
owns the extracted definitions; no new mathematical assertion or proof was added.

Validation: tools/land_set.sh compiles the two files separately through
tools/lean_file.sh with a 60 second limit and checks imports, recording one interface
landing for the normal global-build verification. No lake build was invoked.
No dispatcher, admission, review or landing tool was modified. Q34 should rebase
the metadata, omit these now-landed shared modules/records from its delivery, keep
the corrected ExactBarConeBoundaries module, and cite the landed definition node.
The original H2/H3/H4 return remains pending independent review of that delivery.
