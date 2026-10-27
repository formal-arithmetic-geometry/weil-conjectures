## Worker report

The module `Sheaf.CategoryTheory.DgHomotopicallyProjectiveHomDerived` states
`CategoryTheory.DgAlgebra.homotopicallyProjective_hom_derived_bijective` with
`sorry`. The item's mathematical statement, proof plan and proof dependencies
are unchanged. Its statement dependencies gain the two already landed DG
foundation definitions and the two missing definitions supplied here.

Hypotheses and clauses, read against the complete node statement:

- The size convention is explicit `universe u`. Component groups are
  `ModuleCat.{u} (ULift.{u} ℤ)`; integer cochain complexes and their monoidal
  products are the existing `DgAlgebra.Complex`. No independent smaller test
  universe or size restriction on a family of modules is introduced.
- An arbitrary associative unital integer DG algebra is `(A : Algebra.{u})`.
  `Algebra` is the existing monoid object in these complexes: its chain-map
  multiplication encodes the signed Leibniz identity, its monoid laws encode
  unit and associativity, and its differential squares to zero. No commutativity
  instance is present.
- `(P N : RightModule A)` uses the existing right module objects in the reversed
  tensor category. Thus their action is M tensor A to M with the node's signed
  Leibniz rule; the module morphisms are exactly degree-zero right-linear chain maps.
- The node's homogeneous Hom families use the existing
  `CochainComplex.HomComplex.Cochain` on the underlying integer complexes.
  `DgAlgebra.IsRightLinearCochain` restricts these to f(xa)=f(x)a, without a sign.
  A morphism over ULift integers is equivalently an additive map; it adds no
  coefficient-linearity assumption. `HomComplex.δ r (r+1)` is precisely
  d_N f - (-1)^r f d_P: its formula has coefficient (r+1).negOnePow on f d_P.
- Homotopical projectivity is the new `IsHomotopicallyProjective A P`.
  It quantifies over every right DG target with acyclic underlying complex and
  every `r : ℤ`. Every closed right-linear cochain must have a right-linear
  primitive in degree r-1. This is exactly zero cohomology in every degree of
  the restricted Hom complex, expressed by cycles and boundaries, with no
  substitute ordinary-complex K-projectivity hypothesis.
- `HomotopyCategory A` is the existing quotient by `homotopyRel A`, which uses
  right-linear chain homotopies f-g=dh+hd. Thus its morphisms are the H^0 of the
  specified right-linear Hom cochains. `(homotopyQuotient A).obj P` and the
  corresponding expression for N are these actual objects in the quotient.
- `Derived A` is the already defined Gabriel--Zisman quasi-isomorphism
  localization. The node defining it explicitly identifies it with localization
  of the homotopy quotient. We retain this exact category, not a second model
  or the derived category of ordinary modules over an underlying ring.
- The added `homotopyDerivedFunctor A` is `Quotient.lift` of the existing `Q A`.
  It sends [f] to Q(f), with exactly the existing object values. The only
  postponed construction proof is `Q_map_eq_of_homotopy`, a property explicitly
  stated in its owning definition node and supplied with a cylinder proof
  docstring. The functor data are actual quotient data, never a choice of an
  arbitrary functor or map from a mere existence statement.
- The conclusion is `Function.Bijective ((homotopyDerivedFunctor A).map : ...)`,
  with domain Hom_K(qP,qN) and codomain Hom_D(LqP,LqN). It states both injectivity
  and surjectivity of the precise canonical map requested.
- The distinguished cone triangulation is supplied by the already recorded
  foundation and the proof-only import `DgHomotopyAcyclicLocalization`; the
  Hom-bijection assertion itself needs no extra triangulation binder. There are
  no boundedness, freeness, countability, nonzero or finite-generation binders.

Dependency declarations read and reused (all names below are in
`CategoryTheory.DgAlgebra` unless otherwise indicated):

- `Sheaf.CategoryTheory.DgAlgebraDerivedCategory`: `Complex`, `Algebra`,
  `RightModule`, `underlying`, `act`, `quasiIsomorphisms`, `Derived`, `Q`;
  `DerivedStructure`, `ShiftComparison` and `ConeComparison` document the
  already specified standard derived structure and signs.
- `Sheaf.CategoryTheory.DgAlgebraHomotopyStructure`: `homotopyRel`,
  `HomotopyCategory`, `homotopyQuotient`, `homotopyAcyclic`, `HomotopyStructure`.
- `Sheaf.CategoryTheory.DgBimoduleModels`: `rightAction`,
  `homogeneousAction`, `IsRightLinearCochain`. Its existing
  `IsHomotopicallyInjective` is the dual condition, not a definition of
  homotopical projectivity.
- Proof import `Sheaf.CategoryTheory.DgHomotopyAcyclicLocalization`:
  `HomotopyStructure.AcyclicLocalization` and `homotopy_acyclic_localization`.
- Proof import `Mathlib.CategoryTheory.Triangulated.Orthogonal`:
  `CategoryTheory.ObjectProperty.leftOrthogonal.map_bijective_of_isTriangulated`
  is the exact Mathlib match recorded by the other proof dependency. Its full
  signature and the definition of left orthogonality were read.
- `Mathlib.CategoryTheory.Quotient`: `Quotient.lift` gives the canonical descent.
  `Mathlib.Algebra.Homology.HomotopyCategory.HomComplex`: `Cochain`, `δ` give
  actual homogeneous additive maps and their signed differential.
- `def-weil-size-convention` is recorded as a convention without a Lean
  declaration; its requirement is implemented by explicit universe polymorphism.

Source check: read local Stacks `dga.tex`, definition-unbounded-derived-category
and lemma-hom-derived (09KX/09KY), including the proof of part (1). Its only
input on the source module in the comparison argument is the asserted vanishing
against acyclic cones and all their shifts. The node's Hom-complex hypothesis
supplies exactly that input, as its accepted proof plan explains.

Edge cases checked before writing:

- P=0: all right-linear Hom cochains vanish, hence the projectivity predicate
  holds; the source and target Hom sets in the conclusion are singleton sets.
- N=0: the Hom comparison concerns the singleton zero Hom sets.
- The zero algebra is permitted: unital modules are zero, with the same result.
- A=ℤ in degree zero recovers the usual K-projective comparison for ordinary
  complexes, but is not used as a restriction on the algebra.
- Unbounded P, N and A, arbitrary integer r (including negative r), nonzero
  algebra differential and noncommutative multiplication are all allowed.
  For right-linear f, δf remains right linear: the terms involving d_A(a)
  cancel with the opposite signs. In degree -1, δh=dh+hd as required.
- Acyclic targets are not assumed contractible. The definition still demands
  vanishing of the restricted Hom cohomology for those targets. Using ordinary
  underlying K-projectivity or ordinary homotopies would change this condition,
  so neither was substituted.
- The cylinder used to justify the quotient lift has differential
  (dy+x,dz-x,-dx); its two inclusions are equal after inversion of its projection.
  Its third, shifted component retains the unchanged right action, so this
  argument also respects the right-module convention when d_A is nonzero.

Searches for existing definitions and statements:

- `loogle` query `CochainComplex.IsKProjective.Qh_map_bijective, CategoryTheory.ObjectProperty.leftOrthogonal.map_bijective_of_isTriangulated`: 0 hits; .
- `leanfinder` query `Homotopically projective differential graded modules morphisms homotopy category derived category bijective`: 8 hits; CochainComplex.IsKProjective.Qh_map_bijective, CochainComplex.IsKInjective.Qh_map_bijective, CochainComplex.HomComplex.CohomologyClass.bijective_toSmallShiftedHom_of_isKProjective, CochainComplex.isKProjective_iff_leftOrthogonal, DerivedCategory.instHasLeftCalculusOfFractionsHomotopyCategoryIntUpQuasiIso, DerivedCategory.instHasRightCalculusOfFractionsHomotopyCategoryIntUpQuasiIso, HomotopyEquiv.isKProjective, CochainComplex.IsKProjective.leftOrthogonal.
- `grep` query `DGModule|DGAlgebra|IsKProjective`: 10 hits; Mathlib/Algebra/Homology/HomotopyCategory/KProjective.lean, Mathlib/Algebra/Homology/HomotopyCategory/KProjective.lean, Mathlib/Algebra/Homology/HomotopyCategory/KProjective.lean, Mathlib/Algebra/Homology/HomotopyCategory/KProjective.lean, Mathlib/Algebra/Homology/HomotopyCategory/KProjective.lean, Mathlib/Algebra/Homology/DerivedCategory/KProjective.lean, Mathlib/Algebra/Homology/DerivedCategory/KProjective.lean, Mathlib/Algebra/Homology/DerivedCategory/KProjective.lean.
- `leansearch` query `differential graded module homotopically projective right linear cochains`: 8 hits; CochainComplex.IsKProjective.mk, HomotopyEquiv.isKProjective, CategoryTheory.ProjectiveResolution.instProjectiveXIntCochainComplex, CochainComplex.HomComplex.δ_ofHomotopy, CategoryTheory.instLinearHomotopyCategoryMapHomotopyCategory, CategoryTheory.ProjectiveResolution.cochainComplex_d, CochainComplex.HomComplex.δ_hom_apply, CategoryTheory.ProjectiveResolution.liftHomotopy.
- `leanfinder` query `Localization functor for differential graded modules identifies homotopic maps and descends to homotopy category`: 8 hits; ComplexShape.quotient_isLocalization, instIsLocalizationHomologicalComplexIntUpHomotopyCategoryQuotientHomotopyEquivalences, HomologicalComplexUpToQuasiIso.Qh, instIsLocalizationHomologicalComplexDownHomotopyCategoryQuotientHomotopyEquivalences, HomologicalComplexUpToQuasiIso.Q_map_eq_of_homotopy, HomologicalComplexUpToQuasiIso.instIsLocalizationHomotopyCategoryQhQuasiIso, DerivedCategory.Q_map_eq_of_homotopy, ComplexShape.QFactorsThroughHomotopy.areEqualizedByLocalization.
- `grep` query `homotopy.*Q|Q_map_eq_of_homotopy|IsHomotopicallyProjective`: 25 hits; Mathlib/Topology/Homotopy/Path.lean, Mathlib/Topology/Homotopy/Path.lean, Mathlib/Topology/Homotopy/Path.lean, Mathlib/Topology/Homotopy/Path.lean, Mathlib/Topology/Homotopy/Path.lean, Mathlib/Topology/Homotopy/Product.lean, Mathlib/Topology/Homotopy/Product.lean, Mathlib/Topology/Homotopy/Contractible.lean.
- `leansearch` query `Localization of differential graded modules identifies homotopic right linear maps`: 8 hits; LocalizedModule.lift, IsLocalizedModule.mapExtendScalars, HomotopicalAlgebra.RightHomotopyRel.factorsThroughLocalization, ComplexShape.QFactorsThroughHomotopy.areEqualizedByLocalization, IsLocalizedModule.mapEquiv_apply, IsLocalization.map_eq_toLinearMap_mapₐ, IsLocalizedModule.lift, IsLocalizedModule.linearEquiv_apply.

The ordinary-complex `CochainComplex.IsKProjective.Qh_map_bijective` search hit
is not an arbitrary-DG-algebra statement. The generic orthogonality theorem
is already the exact recorded proof leaf and is imported rather than restated.
The quotient-lift searches found ordinary-complex Qh and homotopy equality
lemmas, not the DG-module factorization constructed here.

Local `rg` searches covered DG modules/algebras, Hom cochains, projectivity,
Qh, homotopy-localization functors and the item id in both `lean/WeilConjectures`
and `lean/Sheaf`; no exact existing statement was found. Reading the landed
DgBimoduleModels definitions found precisely the right-linear cochains needed
by the new predicate, and its injective dual. A scan of all DAG definition
statements/titles for homotopical projectivity and homotopy-derived functors
found no node for either missing definition; the related coherent-localization,
filtered, two-step and Mayer--Vietoris definitions are different notions.
`tools/blueprint_refs.py search` returned zero for `dg homotopically projective`,
`homotopically projective`, and `dg homotopy derived functor`.
`tools/blueprint_refs.py ancestor` reports no imported ancestor, hence the new
nodes retain `blueprint.from.node: null` and prepend this item to the inherited via.

No statement correction and no STATEMENT-DISPUTED fault were necessary.
Every postponed theorem is `sorry` with a complete proof docstring. There are
no hollow data definitions. All three modules compiled cleanly through
`scompile.py`, separately and in dependency order, including their library module
identities; the final compile output contained no errors or warnings.

## New nodes

`def-sfb-dg-homotopically-projective` owns module
`Sheaf.CategoryTheory.DgHomotopicallyProjective` and the Prop-valued definition
`IsHomotopicallyProjective`. It states acyclicity of right-linear Hom cochains
into every acyclic target by the explicit cycles/boundaries criterion. It uses
existing cochains, differential and right-linearity. Source: the vanishing
condition in Stacks dga.tex 09KM/09KY. The recorded LeanSearch, LeanFinder,
Loogle and grep searches found only the ordinary-complex specialization;
DAG/blueprint and project searches found no definition of this predicate.

`def-sfb-dg-homotopy-derived-functor` owns module
`Sheaf.CategoryTheory.DgHomotopyDerivedFunctor`. It states that the existing
quasi-isomorphism localization identifies right-linear homotopies and defines
its canonical descent from the existing homotopy quotient. Source: Stacks
dga.tex 09KW/09KX. Its `Q_map_eq_of_homotopy` named well-definedness theorem
matches the explicit assertion in this node's statement and has the cylinder
proof in its docstring; `homotopyDerivedFunctor` has actual `Quotient.lift` data.
The recorded LeanSearch, LeanFinder and grep searches found only ordinary
cochain-complex results. Neither existing DG foundation module provides this
descent, and DAG/blueprint searches found no separate definition node.

The first preflight required `import_flags` on both new definition nodes; added
the empty list required by the live node schema and reran the dry run.

## Second reading by N5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
