# Q73 prerequisite extraction maintenance

The returned stage-2 item lem-per-local-blowup-tower-globalization@d65efc968
failed repeatedly although all three retained modules compiled. The return
requires giving OrdinaryTowerCartesianMap a definition owner and removing the
normalization theorem from the item's statement dependencies. That extraction
also edits NormalizedTowerRegularPullback, which is outside the resulting item
prerequisite closure. stage2_delivery therefore excludes its node and rejects
its module with "no node of the delivery has it as lean.file". deliver2.py also
drops dependency-node stmt_deps changes. These two packet rules do not support
the explicitly requested extraction in a single delivery.

Maintenance applies only the prerequisite extraction directly under the merge
lock. The new definition module is copied from the retained Q73 repair. Its
structure signature and all five fields match the old structure byte for byte.
The normalization module only adds the public import and removes that structure.
Its node gains the definition dependency, removes the moved declaration from
lean.declarations and explains the ownership change. Existing lean.by and all
mathematical statement, proof, source and review fields are preserved.

Both changed Lean modules are checked separately with tools/lean_file.sh and
its 60-second per-file limit before committing. Incremental graph validation
checks the two affected records. Backups of existing files are adjacent with
suffix .maint-Q73-1792824291.bak; newly created files have adjacent content
snapshots with that suffix and are listed as previously absent in the local
maintenance payload. No protected pipeline tool is changed.

The worker should remove these four now-landed prerequisite files from its
packet (keeping .bak copies), retain its globalization module and item node,
compile and run the prescribed deliver2.py dry run again. The outstanding Q73
return and original delivery branch remain for the normal independent review.
The local REPORT.md records the commit, verification and protected-tool fix
needed for future extractions.
