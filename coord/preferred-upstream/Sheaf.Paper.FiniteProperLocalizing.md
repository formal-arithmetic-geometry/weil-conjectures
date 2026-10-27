## Our earlier proof of this module (recovered from git history, 2026-10-23)

`coord/preferred-upstream/Sheaf.Paper.FiniteProperLocalizing.lean` is this module at commit `5a4b067a363` (`git show 5a4b067a363:lean/Sheaf/Paper/FiniteProperLocalizing.lean`), where `finiteOpenLocalizing` was proved (statement unchanged since then). The green fix `74dda455c88` after the 10-19 upstream sync replaced the proof by `sorry` (it went through `openImmersionLowerShriek_localizing`, which no longer compiled then). The module is now in quarantine (rework row of the 58206abfd sync).

Re-apply on the current text: put that proof back (16 lines, adapting it to the current context) when the module is reworked, and deliver as usual. Do not restore the old file wholesale.
