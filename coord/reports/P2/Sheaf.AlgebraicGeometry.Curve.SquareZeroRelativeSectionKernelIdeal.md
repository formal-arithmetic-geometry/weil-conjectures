## What changed

Proved `AlgebraicGeometry.Scheme.relativeSectionKernel_ker_mul_le_bot` in
`Sheaf.AlgebraicGeometry.Curve.SquareZeroRelativeSectionKernelIdeal`, with its original
signature and visibility unchanged. Added the proof-only import
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial` and the completely
proved private helper `square_zero_global_kernel`.

The relative inclusion kernel is `I.comap J.subschemeι`: pushing it forward recovers
`I`, and pulling back along the closed immersion recovers the kernel. Multiplicativity
and monotonicity of ideal-sheaf pullback send `I*I ≤ J` to square-zero on the
J-subscheme, and then on every base change. The helper restricts two global kernel
sections to affine opens, uses the square-zero inclusion there, and applies scheme
sheaf separatedness to their product. No surjectivity of global restriction is assumed.
Updated the existing node's proof and proof_origin to describe these actual Lean steps;
its two definition dependencies remain sufficient. No new nodes or interface changes.

Searches through the prescribed msearch wrapper: Lean Finder for square-zero kernels
of base-changed closed immersions returned `ker_fst_of_isClosedImmersion`; Loogle for
`RingHom.ker, Ideal.mul` returned an unknown-identifier result for `Ideal.mul`; grep for
kernel/pullback/inclusion combinations located the ideal-sheaf kernel formulas.
Repository searches found the already-proved `comap_mul`, `comap_subschemeι`, and
`comap_map_of_isClosedImmersion` in the added source-library import.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.relativeSectionKernel_ker_mul_le_bot`
(node `lem-sc-square-zero-relative-section-kernel-ideal`).
The private helper is also proved. No remaining sorry in the item and no new holes.
This is a proof, not a decomposition. The file compiles cleanly with lcompile.py.

Edge cases require no exclusions: when I=J the relative kernel vanishes; when I=0,
hJI forces J=0; the empty scheme or empty test scheme is handled by sheaf
separatedness with an empty pointwise condition. No nilpotence, affineness of the
whole test scheme, or extra assumptions on X were introduced.

## No longer needed

None. Both original public imports are needed for the unchanged statement.
The new import is used only in the proof. No planned dependency node or module is
pruned; the proof replaces the informal affine quotient/base-change calculation by
already-proved ideal-sheaf identities. The unit record sk-prop-h2 has no realized
nodes for this item, and its route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original plan cited only definitions while leaving the affine and gluing work
implicit. The available source-library pullback identities close the geometric part;
`Hom.ker_apply` and sheaf separatedness close the global-section part. The DAG now
records these concrete arguments and declaration names. No statement is disputed.
The cited blueprint file is absent from this machine's literature checkout; the
existing statement and docstring were preserved, and no new sourced hole was added.

## Second reading by P2

1. Compared the sole delivered Lean module against the repository with `diff -u`.
   The existing theorem signature, universe, namespace, visibility, and docstring are
   byte-for-byte unchanged. There are no definition edits, change records, or forced
   adaptations. Verdict: pass.
2. Independently compiled the module with `lcompile.py`: clean, 3.5 seconds.
   Compiled a scratch copy with `#print axioms` for both the private helper and
   `AlgebraicGeometry.Scheme.relativeSectionKernel_ker_mul_le_bot`; each uses exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Read all proof
   steps: kernel restrictions follow from naturality, products vanish on an affine
   neighborhood of each point, and separatedness gives global vanishing. No forbidden
   declaration or unproved data choice occurs. Verdict: pass.
3. No statements were split off and no holes were added. The completely proved
   private helper only transfers an ideal-sheaf inclusion to global sections; it does
   not restate the item. Its quasi-compactness assumption supplies `Hom.ker_apply`,
   and holds for the closed immersion used by the main proof. Checked I=J, I=0,
   J=0 with I square-zero, and empty test schemes; none needs an extra hypothesis.
   Verdict: pass.
4. Read the imported source-library pullback identities and Mathlib kernel formulas.
   Independent Lean Finder search for quasi-compact morphisms with square-zero kernel
   on global sections returned `Hom.ker_apply` and the affine-only `ker_of_isAffine`,
   but no replacement for the nonaffine separatedness argument. Repository searches
   likewise found no shorter complete theorem. The new Functorial import is proof-only;
   the original imports supply objects in the unchanged signature. Both old
   `proof_deps` are retained and used, so `No longer needed: None` is complete.
   Read `dag/units/sk-prop-h2.json`: its realized lists are empty, and no unit route
   is bypassed. Verdict: pass.
5. Compared the delivered node with the repository node and read both dependency
   records. Only `proof` and `proof_origin` differ; the four proof steps match the
   Lean kernel identification, two pullback product arguments, and local-to-global
   helper. `proof_deps` is the union of the steps' node citations; the additional
   already-proved library identities are identified by declaration name in the steps.
   There are no new nodes. Verdict: pass.

Second reading changed only this report, adding the independent review and axiom
checks. The Lean proof and node required no repair. One original hole is closed,
zero holes are added, and no modules are pruned.
