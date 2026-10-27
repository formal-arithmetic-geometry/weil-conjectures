## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceSteinFiniteFibresResidueFields` states
`AlgebraicGeometry.AlgebraicSpace.steinAffineProjection_finite_fibres_residueFields`.
Its only theorem has proof `sorry`. It introduces no definitions and changes no
natural-language statement, proof step, or proof dependency.

Source read: `literature/stacks-project/spaces-more-morphisms.tex`, labels
`lemma-stein-universally-closed` (0A19) and
`lemma-stein-universally-closed-residue-fields` (0E1C), lines 7994–8092.
The latter assumes universally closed, quasi-separated, locally finite type,
affine target; the node specializes to proper morphisms, exactly as its source
record says. Its eight-step accepted proof, including the omitted topological
argument via generic points of finite affine charts, is reproduced in the theorem
docstring. There is no statement correction or mathematical dispute.

Hypotheses and clauses, matched individually:

- The arbitrary commutative ring is `(A : Type u) [CommRing A]`; the target
  `T = Spec A` is `Spec (.of A)`.
- The algebraic space is `X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))`.
  The terminal lifted integer spectrum is the existing encoding of absolute
  algebraic spaces; it imposes no scheme-representability assumption.
- The given morphism to the affine target is the binder
  `f : X ⟶ schemeSpace (Over.mk (specULiftZIsTerminal.from (Spec (.of A))))`.
  The unique structural map to the terminal scheme adds no mathematical data.
- Properness is exactly `(hf : MapIsProper f)`. Its defining conjunction is
  separatedness, finite type, and universal closedness. No Noetherianity,
  flatness, local finite presentation, reducedness, or representability is assumed.
- `B = Γ(X_et, O_X)` is `RingCat.sectionsSubring X.smallStructureRings.obj`. This is
  the ring of compatible regular functions on the small affine etale basis,
  with the pointwise commutative ring structure. The affine basis computes
  precisely the global sections on the full small etale site.
- Pullback `A → B` is the recorded `affineGlobalScalar A` with the target
  `Over.mk (specULiftZIsTerminal.from (Spec (.of A)))` and `Iso.refl _`.
  The induced map `π` is written explicitly as `Spec.map` of its
  `CommRingCat.ofHom`. It is not an arbitrary map or chosen factorization.
  `Subring.toCommRing` explicitly supplies the pointwise commutative structure,
  so elaboration does not depend on the instance defined in the theorem module.
- Every base point is the arbitrary binder `(t : Spec (.of A))`.
  The first conclusion `(Spec.map (...) ⁻¹' {t}).Finite`
  is precisely finiteness of the point inverse image.
- The second conclusion quantifies over `z : Spec (@CommRingCat.of (RingCat.sectionsSubring X.smallStructureRings.obj) ...)` and
  the equality `Spec.map (...) z = t`. Its assertion
  `((Spec.map (...)).residueFieldMap z).hom.Finite` uses the
  canonical residue map `κ(π(z)) → κ(z)`, identifying `π(z)` with `t` by that
  equality. `RingHom.Finite` is definitionally finite generation of the target
  module for the algebra induced by that ring homomorphism. For fields this
  is exactly finite dimension. This avoids an arbitrary choice of field action
  and unnecessary dependent casts.
- Point spaces of algebraic spaces retain the recorded final atlas topology.
  The two point sets appearing explicitly in the conclusion are spectra of
  rings, so Mathlib's ordinary scheme points give exactly their prime ideals
  with their Zariski topology; no replacement point encoding is introduced.

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `Scheme.Hom`, `Spec`, and `Spec.map`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsAlgebraicSpace`, `IsRepresentableWith`, `EtaleSite`, and the regular-functions
  `structurePresheaf`/`structureSheaf` definitions.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsProper` and
  its component definitions, including chart tests and universal point closedness.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`, whose domain is `κ(π(z))`.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `RingHom.toAlgebra`.
  `Mathlib.RingTheory.Finiteness.Defs`: `RingHom.Finite`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`,
  with the existing field-valued point classes and final atlas topology.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`:
  `SmallEtaleModel`, `smallStructureSheaf`, `smallStructureRings`.
- `Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections`: `affineGlobalScalar`.
  Their definition nodes `def-sfb-space-small-ringed-model` and
  `def-sfb-space-affine-global-sections` are added to `stmt_deps`.
- `Mathlib.Algebra.Category.Ring.Limits`: `RingCat.sectionsSubring`;
  `Mathlib.Algebra.Ring.Subring.Defs`: `Subring.toCommRing`.
- `Sheaf.AlgebraicGeometry.SpaceSteinFactorizationAffine` is a plain proof import.
  The statement uses none of its declarations: both the section-ring structure
  and spectrum of the scalar map are expanded explicitly. Its theorem node
  remains in `proof_deps`, and is absent from `stmt_deps`.

All recorded modules for stated proof dependencies are imported without `public`,
including the point calculus, affine subatlas/refinement, incomparability,
Noetherian affine schemes, generic points, and scheme permanence interfaces.
The three proof dependencies without a Lean or Mathlib record are not imported:
`lem-sfb-stack-finite-type-calculus`, `lem-sfb-finite-type-points-detect-open`,
and `lem-sfb-finite-type-field-point-characterization`. They are only proof inputs,
so their absence does not affect the current statement.

Edge cases checked before writing: if `A` is the zero ring, there are no base
points and the universal assertion is vacuous; if `X` is empty its global-function
ring is zero, so each point fibre is empty and the residue clause has no points.
An arbitrary empty fibre is allowed by `Set.Finite`. Finite residue extensions
may be inseparable or degree one: there is no separability condition. Nonreduced
and non-Noetherian rings and reducible spaces are not excluded. The single
explicit universe is the usual universe of the algebraic spaces and schemes;
there is no quantification over smaller independent test universes. Proper
projective space over `A` is allowed: the conclusion does not require `f` itself
to have finite fibres.

Searches actually run:

- `msearch.py ... leanfinder`: “The spectrum of global functions of a proper
  algebraic space over an affine scheme has finite point fibres and finite
  residue field extensions”. Eight hits; `finite_appTop_of_universallyClosed`
  requires an integral scheme over a field; other results concern finite scheme
  morphisms. None states this result for algebraic spaces.
- `msearch.py ... loogle`: `"AlgebraicGeometry", "residueFieldMap", "Finite"`;
  zero hits.
- `msearch.py ... grep` in `AlgebraicGeometry`:
  `stein|globalSections.*[Ff]inite|[Ff]inite.*globalSections`; zero hits.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for
  `stein.*[Ff]inite|[Ff]inite.*[Ss]tein|steinGlobalFunctions|steinAffineProjection`:
  found the canonical algebraic-space constructions and the scheme-only theorem
  `Scheme.Hom.steinFactorizationBase_finite_fibres_residueFields`. The latter
  requires an actual scheme, so is not an existing match for this item.
- Exact item-id search in `lean/WeilConjectures`: no match.
- Source search read the definitions and signatures of `RingHom.Finite`,
  `Scheme.residueField`, `Scheme.Hom.residueFieldMap`, and the dependencies above.

Validation uses the prescribed `scompile.py` and `deliver2.py --no-push` wrappers.
The maintainer performs the independent review after delivery.

## Repair of return H2

The returned immutable head was `8b68d584cac6`. Compared with that sandbox version,
this repair removes `lem-sfb-space-stein-factorization-affine` from the added
statement dependencies. The current main node still has only its original seven
statement dependencies and no Lean record, so the repaired copy adds precisely
the two already-recorded definition nodes named above; other main-node fields
are retained. No new node or dependency module is needed.

This follows the maintainer's explicitly offered alternative: state the ring as
`RingCat.sectionsSubring X.smallStructureRings.obj` and the projection as
`Spec.map` of `affineGlobalScalar`, citing their definition owners. The pointwise
commutative ring instance is now an explicit `Subring.toCommRing` argument.
The source expressions are definitionally the old ring and projection, so both
conclusions and every hypothesis are unchanged mathematically. There is no use
of the factorization theorem's conclusion in the statement. Its module is now
imported privately for the existing step 1 of the proof plan only.

The first repair compile accepted the explicit constructions and identified
an overlong line. Wrapping the residue-map projection required using its fully
qualified function name `Scheme.Hom.residueFieldMap`; this preserves its type.
All lines were checked against the 100-character limit before final compilation.

## Second reading by Q89

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
