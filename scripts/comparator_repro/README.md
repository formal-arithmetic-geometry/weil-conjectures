# Fast comparator kernel replay (Lean 4.33.1)

Run on Weil in an already-built project tree. This does not run `lake build` or modify
project artifacts. `Replay.lean` imports only Lean; it reads the target's exported,
server, and private olean parts, imports its dependencies, then sends its declarations
through the kernel at trust level zero. It uses Lean's dependency-first replay algorithm,
including mutual inductives and constructor/recursor validation. Each actual kernel
addition prints flushed `BEGIN` / `END` lines and nanosecond wall timings.
Imported environments use Lean's `leakEnv` option: they remain alive until this standalone
process exits, avoiding reference-count and thread-sharing traversals of the imports.
Visibility and trust-level-zero checks of target declarations are unchanged.

```sh
python3 scripts/comparator_repro/watchdog.py --seconds 120 -- \
  lake env lean --run scripts/comparator_repro/Replay.lean \
  WeilConjectures.AlgebraicGeometry.EtaleBaseChangeRestrictScalars private
```

The watchdog kills the entire process group and returns 124 if a declaration exceeds its
wall limit. Its startup limit is separately configurable with `--startup-seconds`,
and its total process limit is 600 seconds by default (`--total-seconds`).
The script must finish with `COMPLETE` and exit 0 to claim success. Imported dependencies
are trusted as already built; this is a diagnostic, not full comparator certification.

Modes (second positional argument after the target module):

- `private`: all dependency bodies, matching comparator visibility.
- `exported`: ordinary module-system imports, the build control.
- `mixed MODULE...`: exported imports plus `import all` for the listed dependency modules.
- `type-first`: private replay preceded by a checked identity `T → T` for every theorem
  type `T`. The identity is an independent diagnostic and is not used as the theorem proof.
- `mixed-types MODULE...`: combines the preceding two modes.
- `axioms`: follow all target and dependency proof bodies, including opaque values, and
  fail unless every axiom is `propext`, `Classical.choice`, or `Quot.sound`.
- `audit`: report newly visible definitions in the kernel-relevant closure. Traverse
  imported theorem types but not their opaque proofs; traverse the target's own proofs.
  The printed depth is the first DFS discovery depth, not shortest distance.
- `fresh`: replay every loaded dependency and target declaration into an empty environment.
  This is slower and was unnecessary for reproducing the present stall.
- `normalize`, `lets`, `mdata`: optional export-expression controls (not needed for the
  visibility result). `normalize` does both transformations, `lets` only clears let
  `nonDep` flags, and `mdata` only removes metadata. These preserve mathematical content.

For the isolated stall, use:

```sh
python3 scripts/comparator_repro/watchdog.py --seconds 20 -- \
  lake env lean --run scripts/comparator_repro/Replay.lean \
  WeilConjectures.AlgebraicGeometry.EtaleBaseChangeRestrictScalars mixed \
  WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
```

To prevent a concurrent source build from changing the target under test, copy its
`.olean`, `.olean.server`, and `.olean.private` files to a scratch directory, retaining
filenames. Set `CL953_OLEAN` to the copied `.olean`. Dependencies still come from the
built project's normal search path. Record the source revision and all three SHA256s.

The first private/exported pair used CL952's acfd0423983 artifacts: the same helper
exceeded 120 seconds in private mode and completed in 30.806 ms in exported mode.
Whole-process times were 169.612 s and 7.483 s. The first private run used the initial,
slower two-import loader; the current loader reads the target's three files directly.
See `results/` and `U9PROGRESS.md` for subsequent tests and candidate revisions.

To test one changed dependency against an unchanged target snapshot, set
`CL953_REPLACE_MODULE` to its full module name and `CL953_REPLACE_OLEAN` to its scratch
`.olean` path. All three olean parts and both IR parts must be present. This uses Lean's
`ImportArtifacts` map, and changes no other dependency. Prepending a partial root tree to
`LEAN_PATH` does **not** work: Lean would shadow all modules of that root namespace.

If the built tree lacks artifacts needed only by private imports, `CL953_EXTRA_ARTIFACTS`
can name a text manifest with one `MODULE<TAB>OLEAN` pair per line. Each entry supplies
the same five artifact parts as the single replacement above. Snapshot matching built
artifacts and record their source and artifact hashes; the harness still checks every
target declaration and does not skip missing dependencies.

The source fix is the `irreducible_def` in `MorphismDefs.lean`, plus its checked equation
in `baseChange_app`. Source commits: `8c59edaaf3` and `0dd28f4a82`. No target theorem was
edited. The full private replay of CL952's unchanged 47b4 artifact completes in 14.383 s
with the fix; its stalled helper takes 25.240 ms. See `sealed-private-47b4.txt`.

Final validation also covers the original, unchanged CL953 theorem: private replay
hits its 20-second cap before the repair and checks it in 7.908 s afterward (22.627 s
whole process). The changed defining module's own 48 declarations pass private replay
in 441 ms. The proof-body axiom audit traverses 60,892 declarations and finds exactly
`propext`, `Classical.choice`, and `Quot.sound`. Full comparator acceptance is separate.
