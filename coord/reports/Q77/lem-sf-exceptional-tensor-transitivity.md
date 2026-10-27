## Worker report

The item module is `Sheaf.AlgebraicGeometry.SfExceptionalTensorTransitivity`, namespace
`AlgebraicGeometry.Etale`. It states the canonical tensor composition formula and its
invertibility consequence in `sfExceptionalTensorTransitivity`, and the actual etale
restriction formula in `sfExceptionalTensorEtaleRestriction`. These two theorems are the
only new postponed proofs. Their docstrings give all eight steps of the node's proof.
No natural-language statement correction or new DAG node is needed.

Hypothesis and clause correspondence:

- The finite commutative coefficient ring is `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  The objects `{X Y Z : Scheme.{u}}` are arbitrary schemes and `a`, `b` are their named
  morphisms. The composite is literally `a ≫ b`, eliminating an unnecessary equality
  binder without changing the composite case.
- The three supplied open/proper factorizations are `ca : Compactification a`,
  `cb : Compactification b`, `ch : Compactification (a ≫ b)`. This structure has no qc
  requirement on the open immersion. No finite-type, Noetherian, quasi-compactness,
  boundedness or constructibility class is bound.
- `Ga`, `Gb`, `Gh` and `adja`, `adjb`, `adjh` select the supplied right adjoints and their
  adjunctions on `DerivedCategoryModule A _`, precisely the ordinary unbounded category
  of module sheaves. Existence is already the ambient dependency. These selections add
  no geometric existence hypothesis.
- The left functors are the dependency's `rightDerivedLowerShriekOfCompactification`.
  The helper `sfGraphCompactSupportCompIso` is the actual graph construction, rather
  than a chosen member of a bare `Nonempty` type. `sfExceptionalCompComparison` is
  `conjugateIsoEquiv adjh (adja.comp adjb)` applied to its inverse: hence its components
  are exactly the counit-preserving c of the question, with direction Gh to Gb ⋙ Ga.
- `ha` quantifies over every P in the entire ordinary unbounded category and assumes
  `IsIso (sfEtaleAmbientTensorMap A ca Ga adja P)`, the dependency's actual theta.
- `sfExceptionalCompDelta` is the component c at `constantComplex A Z` followed by
  `inv (sfEtaleAmbientTensorMap ... (Gb.obj (constantComplex A Z)))`. Its target is
  omega_a tensor a*omega_b, with omega_a and omega_b literally Ga(A_Y) and Gb(A_Z).
  The first conjunct asserts `IsIso` of this specified arrow, not merely existence
  of an isomorphism between the two objects.
- The second conjunct states theta_h followed by c_K equals delta tensor identity,
  then `sfExceptionalTensorReassociation`, then identity tensor a*(theta_b), then
  theta_a(Gb K). Lean's composition `≫` writes precisely the displayed equation
  in its execution order. Reassociation explicitly inserts the component of
  `leftDerivedUpperStarComp`, `derivedTensorAssociator`, and the inverse of
  `leftDerivedUpperStarTensorIso`.
- The third conjunct retains the node's tensor-invertibility hypothesis on omega_b:
  there exists V with both omega_b tensor V and V tensor omega_b isomorphic to A_Y.
  Under this hypothesis, for every K, invertibility of theta_b(K) implies invertibility
  of the actual theta_h(K). The hypothesis is mathematically redundant under ha,
  but has deliberately not been removed.
- The restriction theorem binds `[Etale a] [IsSeparated a]`, permitting all separated
  etale a with the supplied factorization, including non-qc open immersions. It uses
  the normalized `sfEtaleRightAdjointComparison` from the etale dependency.
  `sfEtaleDerivedRightAdjointIso` converts that rho to the left-derived model using
  `leftDerivedUpperStarIsoMapDerivedCategory`. The comparison lambda is its whiskered
  inverse followed by c inverse, exactly c inverse rho inverse. This gives an Iso
  `Gb ⋙ L(a*) ≅ Gh`.
- The restriction equation is a*(theta_b) followed by lambda_K equals the canonical
  pullback tensor comparison, followed by lambda_A tensor identity, the inverse
  pullback-composition comparison on the second tensor factor, and theta_h. Its
  source is a*(omega_b tensor b*K) and its target Gh K. This is the node's equation
  with the stated canonical source identification inserted.
- Throughout, inverse image is written as `L(upperStar ...)`, which the already
  recorded canonical `leftDerivedUpperStarIsoMapDerivedCategory` identifies with
  termwise exact inverse image. Thus the restriction equation is on the canonical
  derived model of the same exact functor, and imposes no extra flatness condition.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.SfEtaleAmbientAdjointProjection`:
  `sfEtaleAmbientAdjointProjection`, `sfEtaleAmbientTensorMap` (through the public
  import of the etale dependency). The latter is exactly the inverse-projection /
  counit / unitor adjunct, not an unconstrained comparison.
- `Sheaf.AlgebraicGeometry.SfEtaleUnitTensorArbitraryBase`:
  `sfEtaleRightAdjointComparison`, `sfEtaleRightAdjointUnit`,
  `sfEtaleExactAmbientTensorMap`, `sfEtaleUnitTensorArbitraryBase`. The first and
  last are used to define the normalized restriction Iso.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition`:
  `nonempty_iso_rightDerivedLowerShriek_comp` and
  `nonempty_iso_rightDerivedLowerShriekOfCompactification`, whose full proofs were
  read to expose their graph constructions; also its public proper/open exchange,
  direct-image composition and open-extension composition constructions.
- `Mathlib.CategoryTheory.Adjunction.Basic`: `Adjunction.comp` and its explicit
  composite unit, counit and Hom bijections; `Mathlib.CategoryTheory.Adjunction.Mates`:
  `conjugateIsoEquiv` supplies the exact normalization with real data.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`:
  `leftDerivedUpperStarTensorIso`, `leftDerivedUpperStarIsoMapDerivedCategory`;
  `UpperLowerStar`: `leftDerivedUpperStarComp`.
- `WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`:
  `derivedTensorAssociator`, `derivedTensorLeftUnitor`, `derivedTensorRightUnitor`.
  This is included also for the proof dependency lem-kun-tensor-unit.
- The proof-only dependency lem-sf-etale-compact-projection-coherence has no Lean
  record/module at the time of writing. It is not a statement dependency and no
  duplicate assertion is introduced. Its associativity and compositor equations
  are recorded by name in both theorem proof plans; its future proof import is
  the maintainer's normal responsibility.

Edge cases checked before writing: the zero finite ring is allowed; the empty scheme
and zero derived objects remain in the category; no input is restricted to bounded
objects; identity a or b is permitted; open immersions with non-qc open domain are
permitted. Every composition has matching source and target, checked by Lean.
The consequences concern actual theta morphisms, not merely endpoint isomorphisms.
There is no STATEMENT-DISPUTED issue. The dependency's graph construction uses no
closure of the source in a product and does not invoke compactification existence.

Searches for an existing complete statement:

- msearch leanfinder, query `Canonical exceptional inverse image tensor map compatible
  with composition and etale restriction`: eight hits, including
  `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale` and etale base-change lemmas;
  no exceptional tensor composition/restriction equation.
- msearch loogle, query `"rightAdjoint", "comp"`: twelve hits, including
  `CategoryTheory.Functor.isRightAdjoint_comp` and rigid-category mate composition;
  none states this result. The existing general conjugation construction is reused.
- msearch grep, query
  `sfEtale.*Transitivity|dualizingComplexTensorMap|rightAdjoint.*Comp`: 25 hits in
  Mathlib, on adjoint functors and rigid-category mates, no matching statement.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for
  `sfEtale.*Transitivity|dualizingComplexTensorMap|projectionTensorMap|rightAdjoint.*[Cc]omp`,
  and grep of the item id in `lean/WeilConjectures`: no exact item declaration.
  Read the nearby upstream `Derived/SmoothDuality/Local.lean` composition theorems
  and `UpperShriekCanonicalMapsComposition.lean`; these give endpoint Iso existence
  and invertibility consequences for chosen compact support, rather than this full
  pair of normalized morphism equations for arbitrary supplied models.

Validation: both delivered modules compile separately through scompile.py against the
published live library, in sandbox and library module modes. There were no errors or
warnings. The graph data module compiled in about 5 seconds; the item in 17–21 seconds.

## Dependency modules

`lem-etale-unbounded-compact-support-composition`: the old record pointed solely to
`nonempty_iso_rightDerivedLowerShriek_comp`. That statement proves existence, but does
not expose a specified graph compositor, so it cannot define the canonical c required
by the item's equations without a forbidden arbitrary choice. The delivered module
`Sheaf.AlgebraicGeometry.SfGraphCompactSupportComposition` exposes exactly the two
constructions already used in the upstream theorem proofs as
`sfGraphCompactificationComparison` and `sfGraphCompactSupportCompIso`. It computes
through the graph embeddings in the product of the proper parts, their open
intersection, and proper/open interchange. It never chooses from a bare existence
statement. The only node field repaired is lean, with a note explaining the defect.
The original existence theorem remains publicly imported. All data are constructed;
there are no postponed proofs in this dependency module and no new mathematical
assertions beyond those constructions. Local proof terms certify graph equalities
and properness needed to assemble the data, as in upstream; they are not new
standalone theorem proofs. The canonical graph comparison belongs to this existing
composition notion, so no new definition node is introduced.

## Second reading by Q77

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
