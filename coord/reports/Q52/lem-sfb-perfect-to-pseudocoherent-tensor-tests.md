## Worker report

The module `Sheaf.AlgebraicGeometry.PerfectToPseudoCoherentTensorTests` states
`AlgebraicGeometry.isPseudoCoherent_tensor_sections_of_perfect_tests`, with `sorry`
as its entire proof. No definition or additional theorem is introduced.
The source is Stacks Project, perfect.tex, Tag 0CSH, `lemma-perfect-enough`
(lines 8648 onward in the supplied source). Its full approximation proof is
included, in seven steps, in the declaration docstring.

Hypothesis and conclusion correspondence:

- A commutative ring: `(A : CommRingCat.{u})`, allowing the zero ring.
- A scheme over A: `(X : Scheme.{u}) (p : X ⟶ Spec A)`. This specifies precisely
  the scalar action on sections; no flatness, separation, properness or finite
  presentation of p is assumed.
- X quasi-compact and quasi-separated: `[CompactSpace X] [QuasiSeparatedSpace X]`.
  Mathlib's `quasiCompact_iff_compactSpace` and
  `quasiSeparated_iff_quasiSeparatedSpace` identify these with the morphism
  properties for p, since Spec A is qcqs. These are the absolute scheme
  hypotheses in the node, not separation of p.
- K in D(O_X): `(K : schemeDerivedCategory X)`, using the recorded shared
  sheaf-of-modules carrier, rather than a different category on X.Modules.
- Quasi-coherent cohomology: `(hK : schemeDerivedQCohProperty X K)`.
- Some integer b with H^i(K)=0 for i>b: `(hBound : ∃ b : ℤ, ∀ i : ℤ, b < i →
  IsZero ((DerivedCategory.homologyFunctor ... i).obj K))`. No lower bound is
  imposed and the bound need not be selected in the theorem's inputs.
- Every perfect P: `hTests` quantifies over all `P : schemeDerivedCategory X`
  and assumes `Scheme.IsPerfect X P`.
- RΓ(X,P tensor^L K) pseudo-coherent in D(A):
  `DerivedCategory.IsPseudoCoherent ((schemeDerivedGlobalSections X ⋙
  (affineGlobalSectionsRestriction p).mapDerivedCategory).obj (P ⊗ K))`.
  The tensor uses the global `schemeDerivedTensorMonoidal` instance, namely
  the shared K-flat derived tensor. Sections are the right-derived global
  section functor followed by exact scalar restriction, with ring map
  `((Scheme.ΓSpecIso A).inv ≫ p.appTop).hom`.
- Every pseudo-coherent E: the conclusion universally quantifies over
  `E : schemeDerivedCategory X` with `Scheme.IsPseudoCoherent X E`.
- The conclusion is precisely the same D(A)-pseudo-coherence predicate on
  the same derived section composite evaluated on `E ⊗ K`.

The `HasDerivedCategory` instances provide the localization infrastructure.
The section-ring localization universe wΓ and base-ring localization universe
wA are independent of wX; no equality between them is imposed. Localizations
on the open localized sites use the universe required by the recorded
perfect and pseudo-coherent predicates. Ring and scheme have the usual common
ambient size u, which can be enlarged to contain both.

Dependency declarations used, read with their source signatures and docstrings:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms
  and `Spec`; the morphism-conventions node is a convention without a separate
  declaration. `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` supplies
  the qcqs comparison with `CompactSpace` and `QuasiSeparatedSpace`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory` and `schemeDerivedQCohProperty`.
- `WeilConjectures.AlgebraicGeometry.PerfectComplex`: `Scheme.IsPerfect`.
- `WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex`:
  `Scheme.IsPseudoCoherent`.
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `schemeDerivedDirectImage`, the recorded scheme-direct-image interface;
  actual module-valued sections use the existing global-section specialization.
- `WeilConjectures.AlgebraicGeometry.DerivedTensorStructure`:
  `schemeDerivedTensorMonoidal`.
- `WeilConjectures.RingTheory.RingPseudoCoherent`:
  `DerivedCategory.IsPseudoCoherent`.
- `WeilConjectures.AlgebraicGeometry.GlobalDerivedHom`:
  `schemeDerivedGlobalSections`; its existing owner node
  `def-pc-global-derived-rhom` is added to stmt_deps.
- `Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap` is the recorded
  compatibility import reexporting the upstream module of the same suffix:
  `affineGlobalSectionsRestriction`; its existing owner node
  `def-pc-affine-global-hom-base-change-map` is added to stmt_deps. The composite
  is the existing `affineDerivedGlobalSections`, expanded to allow independent
  localization universes exactly as in the landed consumer
  `PerfectTestsDetectPseudoCoherence.lean`. No new section functor is defined.

All recorded, stated proof dependencies are imported non-publicly. The
standard t-structure Mathlib match is imported as well. The approximation
node `lem-sfb-pseudocoherent-perfect-approximation` has no recorded declaration
in the supplied DAG, so it has no proof import; this does not prevent stating
this theorem. It remains named in the proof docstring and in proof_deps.

Edge cases checked against the source and predicates: X may be empty; K, E
or P may be zero; A may be the zero ring; arbitrary integer upper bounds,
including negative ones, are allowed; K and E need not be bounded below.
The zero-test cases give zero derived sections, a pseudo-coherent object.
Empty X makes the local perfectness and pseudo-coherence predicates vacuous,
as they should be, and its derived sections are zero. No Noetherian,
nonempty, characteristic or finite-dimensional hypothesis has been added.
No mathematical statement correction or STATEMENT-DISPUTED issue was found.

Searches for an existing statement:

- `msearch.py ... leanfinder`: "For bounded above quasi coherent complexes on
  qcqs schemes, pseudo coherent derived global sections of tensor products
  with all perfect complexes imply the same for all pseudo coherent complexes".
  Eight hits, concerning LightCondensed internally projective tensor criteria,
  sheaf abelian/Grothendieck instances and quasicoherent finite presentation;
  none states the theorem.
- `msearch.py ... loogle '"IsPseudoCoherent"'`: zero hits.
- `msearch.py ... grep 'PseudoCoherent|pseudoCoherent|pseudo_coherent'`:
  zero Mathlib hits.
- `rg` of perfect/pseudo-coherent tensor tests in `lean/WeilConjectures` and
  `lean/Sheaf`: definitions, approximation statements, and the stronger
  flat-finitely-presented detection theorem were found, but no declaration
  extending perfect tests to all pseudo-coherent tests. The detection theorem
  explicitly cites this node as a missing proof tool.
- `rg 'lem-sfb-perfect-to-pseudocoherent-tensor-tests'` in those two roots:
  only the detection theorem's proof docstring cites it; no existing statement.
- The upstream-name index was consulted for pseudo-coherence names; the
  actual shared predicates were read in the recorded source modules.

Validation: `scompile.py Q52 lem-sfb-perfect-to-pseudocoherent-tensor-tests`
compiled the delivered module successfully in sandbox and library modes, with
no errors or disallowed warnings. All Lean lines are at most 100 characters.
The delivery dry run and final push run the server preflight and per-file compile again.

## Second reading by Q52

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
