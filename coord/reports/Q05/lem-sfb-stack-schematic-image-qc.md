## Worker report

The module `Sheaf.AlgebraicGeometry.StackSchematicImageQc` states
`CategoryTheory.exists_stack_schematicImage_of_quasiCompact`, with its sole proof
`sorry`. No construction is replaced by an arbitrary choice, and no mathematical
statement has been corrected. Its docstring contains all seven proof steps of the
accepted split, with the source and dependency identifiers.

Hypothesis and conclusion correspondence:

- The base scheme is `{S : Scheme.{u}}`. The stack is
  `X : BasedCategory.{v, w} (Over S)` with `hX : IsAlgebraicModuliStack X`;
  `Y : AlgebraicSpace S` is the algebraic-space target. These use the recorded
  definitions and impose neither finite type, separatedness, nor a DM assumption.
- The map is `f : BasedFunctor X (discreteModuli Y.obj.obj)`. Its only extra
  hypothesis is `hf : IsQuasiCompactAlgebraicModuliMap ... f`. The explicitly
  instantiated test universes contain the scheme site and the source/target
  universes through the maxima in that recorded predicate; setting its two
  additional enlargement parameters to zero imposes no equality on `u`, `v`, `w`.
- Existence of the closed image is `∃ W : ClosedSubspace Y`. This existing
  subtype is a subobject whose scheme base changes are closed immersions, and
  retains its scheme structure. The factor map is `q`, with
  `Nonempty (f ≅ q.comp (discreteModuliMap W.val.arrow.hom.hom))`.
- Smallest means the following universal clause: for every closed subspace `D`
  and every factorization `a`, its comparison isomorphism implies
  `W.val ≤ D.val`. This is inclusion of subobjects, not inclusion of point sets.
- The quasi-coherent ideal is `I : QuasiCoherentIdeal Y`, and
  `I.val = kernelSubobject (moduleStructureMap W.val.arrow)`, together with
  `Epi (moduleStructureMap W.val.arrow)`, says the canonical structure map onto
  the closed subspace's direct image has kernel I and is a sheaf epimorphism.
  Thus its quotient sheaf is O_Y/I = i_*O_W, with its canonical ring structure;
  surjectivity is sheaf-local, not the stronger unsupported surjectivity on
  global sections. These are the already recorded ideal/subspace interfaces.
- The next clause says on EACH etale chart T and EACH regular function r:
  r lies in the image of the ideal inclusion exactly when
  `moduliStructureMapApp hX.1.1 Y f T r = 0`. This is precisely
  I = ker(O_Y -> f_*O_X). The recorded structure map sends r to the compatible
  family of its actual pullbacks, and the recorded direct-image sections
  comparison identifies its value with Gamma(X times_Y T, O). ULift changes
  coefficient universes only, not vanishing or injectivity.
- The topological clause is equality of the range of the closed inclusion's
  `moduliPointMap` with `closure (Set.range (moduliPointMap f))`. The existing
  stack topology agrees canonically with the algebraic-space topology by
  `stack_point_topology` / `moduliSpacePointMap_isHomeomorph`.
- Schematic dominance of q is `∀ T, Function.Injective
  (moduliStructureMapApp hX.1.1 ... q T)`. Objectwise injectivity is exactly
  injectivity of the sheaf map O_W -> q_*O_X.
- Flat base change quantifies over EVERY `Y' : AlgebraicSpace S` and `g : Y' ⟶ Y`
  with `MapIsFlat g`; that predicate tests Mathlib `Flat` on compatible etale
  scheme charts. It provides `W'`, an actual cartesian square
  `IsPullback a W'.val.arrow W.val.arrow g`, a factorization of the canonical
  second projection of `moduliTwoFiberProduct f (discreteModuliMap g.hom.hom)`,
  and the full smallest-closed-subspace property for that projection. Thus the
  image of the base-changed f IS the pullback of W, as a closed subspace.
- The final clause quantifies over EVERY etale `g : W' ⟶ W` and chart T of W'.
  A function killed by pullback along ALL objects of
  `ModuliPushforwardIndex W' (moduliTwoFiberSnd q (discreteModuliMap g.hom.hom)) T`
  must vanish. By the definition of `moduliDirectImagePresheaf` as compatible
  families and the explicit formula for `moduliStructureMapApp`, this is its
  zero-kernel condition. For additive ring maps it is equivalent to injectivity.
  It includes arbitrary etale base changes, not only a chosen covering.

Recorded dependencies used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.IsAlgebraicModuliStack` (through StackQcqsMorphism).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `structureSheaf`, `IsEtale`; these are the existing fppf-sheaf spaces.
- `Sheaf.AlgebraicGeometry.StackQcqsMorphism`:
  `IsQuasiCompactAlgebraicModuliMap` and its complete base-change test universe.
- `Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra`:
  `moduliStructureMapApp`, `ModuliPushforwardIndex`, `moduliChartSchemeMap`, and
  the compatible-family/direct-image construction read in full.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`, with
  `Flat.iff_flat_stalkMap`, used through the recorded `MapIsFlat` interface in
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace`: `ClosedSubspace`;
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIdeal`:
  `QuasiCoherentIdeal` and its imported `moduleStructureMap`.
- `Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen`:
  `moduliPointTopologicalSpace` / `moduliPointMap`.
- `Sheaf.AlgebraicGeometry.OpenModuliSubstack`: `moduliTwoFiberSnd`;
  the original groupoid framework supplies `discreteModuli`,
  `discreteModuliMap`, `moduliTwoFiberProduct` and based functor composition.

The item's stmt_deps gains only four ALREADY LANDED definition nodes:
`def-sfb-space-closed-subspace`, `def-sfb-space-quasi-coherent-ideal`,
`def-sfb-space-morphism-properties`, `def-sfb-stack-point-topological-space`.
They supply the concrete notions used in the conclusions. There are no new nodes
and no dependency repairs.

All stated proof-dependency modules are imported without public, including
`AlgebraicStackFibreProducts`, `AlgebraicStackQuasicompactSurjection`,
`StackChartwiseSmoothEtaleCalculus`, `AlgebraicSpaceIdealClosedSubspaceCorrespondence`,
`StackPointTopology`, Mathlib `IdealSheaf.Subscheme`, and upstream
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`.
The proof dependency `lem-sfb-smooth-space-cover-etale-sections` has no recorded
Lean module, so no import for it is invented. It is still named in the docstring.

Sources read: the node and all six original statement dependencies; full Lean
signatures/docstrings of the imported notions; Stacks stacks-morphisms.tex,
section-scheme-theoretic-image, including cover-upstairs, existence, flat base
change and topology; and the current blueprint's direct-images proof. The auxiliary
lemma is not itself a blueprint unit statement. No source-based correction was needed.

Edge cases checked before writing:

- Empty X: W is the empty closed subspace, I is the unit ideal; the target ring of
  sections on an empty base change is zero, so its kernel is all regular functions.
- Identity f: W = Y, I = 0; dominance and all identity/base-change clauses hold.
- A nilpotent closed immersion retains its ideal; topological closure alone is not
  used as a substitute for the image scheme structure.
- Non-quasi-separated X: no quasi-separated hypothesis is imposed on f or X.
  The proof applies the dense flat-pullback theorem only to affine scheme maps.
- Flat g need not be faithfully flat, surjective, or of finite presentation; empty
  base changes and arbitrary non-surjective etale maps are included.
- Independent source category universes v and w are retained. All binders are
  explicit and `autoImplicit false` is set. There are no hidden lets/local notation.

Searches for an exact existing statement (2026-10-24):

- msearch.py leanfinder, query "Quasi compact morphism from algebraic stack to
  algebraic space has schematic image with kernel ideal commuting with flat base
  change": eight hits, all scheme-only (`Scheme.Hom.ker_apply`,
  `Scheme.instQuasiCompactToImage`, etc.); no stack theorem.
- msearch.py loogle, query "AlgebraicGeometry.Scheme.Hom.ker,
  AlgebraicGeometry.Scheme.Hom.image": one hit `Scheme.Hom.toImage_app`, scheme-only.
- msearch.py leansearch, query "The scheme theoretic image of a quasi compact
  algebraic stack morphism to an algebraic space is cut out by the kernel and
  commutes with flat base change": eight hits, all scheme-only, including
  `Scheme.Hom.image`, `Scheme.Hom.support_ker`, `Scheme.Hom.ker_apply`.
- msearch.py grep, pattern `schematic.*[Ii]mage|[Ii]mage.*schematic` in
  AlgebraicGeometry: zero hits. Direct rg in upstream WeilConjectures for
  schematic-image spellings and the item id gave no matching stack statement.
- Direct rg in lean/Sheaf found `exists_qcOpen_schematicClosure`, which is only
  for quasi-compact OPEN IMMERSIONS of algebraic spaces, and
  `AdequateClosedSubstackAffinization`, which assumes adequate moduli data. Neither
  states this general quasi-compact stack-map theorem. Existing notions of
  ideals, closed subspaces, direct image, topology and flatness are reused.

Validation: scompile.py compiled both its private sandbox module (29.7 s) and
`Sheaf.AlgebraicGeometry.StackSchematicImageQc` (4.0 s), exit 0, with no errors
or warnings. Maximum Lean line width is 91 characters. The only postponed
statement is the theorem listed above. Dry-run and delivery results follow below.

The prescribed deliver2.py dry run passed preflight and server compilation:
`OK (dry run): commit 8d76980520f passes the preflight and compiles; nothing pushed`.
The actual delivery runs those same checks again against the current base.

## Second reading by Q05

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
