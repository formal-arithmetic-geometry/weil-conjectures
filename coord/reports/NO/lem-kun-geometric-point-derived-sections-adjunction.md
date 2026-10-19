## Worker report

Item: `lem-kun-geometric-point-derived-sections-adjunction`.
Module: `Sheaf.AlgebraicGeometry.GeometricPointDerivedSectionsAdjunction`.

The module constructs `AlgebraicGeometry.Etale.geometricPointDerivedSectionsIso` and states
`AlgebraicGeometry.Etale.geometricPoint_derivedSections_adjunction`, with `sorry` as its
only postponed proof. All helper definitions have actual data obtained by composition,
canonical derived-functor comparisons, and uniqueness of right adjoints. There are no new
DAG notions, dependency replacements, statement corrections, or disputed statements.

Hypotheses and clauses, matched with the node:

- Algebraically closed field Ω: `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]`.
  The point s is exactly `Spec (.of Ω)`; its geometric point is the identity.
- Arbitrary scheme Z and morphism h: `{Z : Scheme.{u}} (h : Z ⟶ Spec (.of Ω))`.
  There are no assumptions on this morphism. The universe u is arbitrary; sites have
  their standard object/morphism sizes and coefficients occupy u+1. Universes can be
  enlarged to include both the field and the scheme.
- Abelian sheaves and D(ℤ): the coefficient category is
  `ModuleCat.{u + 1} (ULift.{u + 1} ℤ)`, exactly as in the recorded geometric-point
  equivalence, with its fixed ordinary integer tensor. This is the dependency's
  integer-module encoding of abelian groups, not an extra coefficient restriction.
- S_D and C_s: `(geometricPointStalk Ω).mapDerivedCategory` and
  `(geometricPointConstants Ω).mapDerivedCategory`. The public additivity instance
  registers the proof already supplied by the dependency's normalized data theorem;
  no new additivity assertion is postponed. Exactness of the actual stalk is supplied
  by the existing point functor instances.
- The normalized equivalence adjunction: `geometricPointSectionsStalkAdjunction Ω`
  selects the dependency's `adjunction`. Its unit is fixed by `unit_eq`, and its counit
  is uniquely fixed by `counit_unique`. Thus this choice cannot select an arbitrary
  counit or arbitrary sheaf functor. Mapping this adjunction to derived categories is
  exactly the dependency's termwise normalized derived adjunction.
- C_Z: `(constantSheaf Z.smallEtaleTopology (ModuleCat …)).mapDerivedCategory`.
  This is the localization of `Functor.mapHomologicalComplex` applied to the recorded
  constant-sheaf functor. Its adjunction `geometricPointSectionsConstantAdjunction Z`
  is the recorded `derivedConstantGlobalSectionsAdjunction`, transported through
  `leftDerivedFunctorIsoMapDerivedCategory`; hence its counit is the specified ε^Z.
- h⁻¹ and Rh_*: `(upperStar … h).mapDerivedCategory` and
  `(lowerStar … h).rightDerivedFunctor`. Their adjunction is the recorded
  `derivedUpperStarLowerStarAdjunction`, transported through the canonical exact
  comparison, in `geometricPointSectionsImageAdjunction Ω h`. This retains ε^h.
- RΓ_Z is the recorded `rightDerivedGlobalSections … Z`; it is not replaced by
  ordinary termwise sections on an arbitrary unbounded complex.
- γ is `geometricPointSectionsConstantsIso Ω h`: first inverse to
  `mapDerivedCategoryCompIso`, then `mapDerivedCategoryNatIso` of the existing
  `Scheme.upperStarConstantSheafIso`. It is the canonical pullback-of-constants
  comparison from `lem-kun-pullback-constant`, in the direction h⁻¹C_s → C_Z.
- Existence and naturality of β: `geometricPointDerivedSectionsIso Ω h` has type
  `Rh_* ⋙ S_D ≅ RΓ_Z`. It is constructed directly by composing the normalized
  point adjunction with the image adjunction, transporting the left adjoint by γ,
  and applying `Adjunction.rightAdjointUniq` against the constant-section adjunction.
  Thus naturality and invertibility are actual fields of the constructed natural
  isomorphism, with no arbitrary objectwise isomorphisms selected from existence.
- The explicit counit identity is the theorem's first conjunct, universally quantified
  over `E : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat …))`. Lean writes
  composition in traversal order: `γ.app (S_D(Rh_*E)) ≫ C_Z.map (β.hom.app E) ≫ ε^Z_E =
  h⁻¹.map (ε^s_(Rh_*E)) ≫ ε^h_E`. This is exactly the displayed node equation, including
  the arguments of each counit and the direction of γ.
- For a sheaf G in degree zero, the second conjunct uses
  `(DerivedCategory.singleFunctor _ 0).obj G` and `homologyFunctor … 0`.
  `geometricPointSectionsImageH0Iso Ω h G` is the canonical augmentation comparison
  H⁰(S_D Rh_*G[0]) ≅ S(h_*G), using exact-stalk homology commutation followed by
  `homologyRightDerivedFunctorObjSingleFunctorIso G 0` and `rightDerivedZeroIsoSelf`.
  `geometricPointSectionsGlobalH0Iso Z G` uses the same canonical right-derived
  augmentation comparisons for Γ_Z.
- The actual global-section-to-germ map is `geometricPointSectionsGerm Ω (h_*G)`.
  It is `Sheaf.ΓNatIsoSheafSections` at the terminal étale object followed by
  `Point.toPresheafFiber` at the pointed identity neighbourhood. The `ULift.up` merely
  reindexes that same neighbourhood in the dependency's chosen stalk universe.
  `lowerStarCompGlobalSectionsIso … h` is the canonical identification
  Γ_s(h_*G) = (h_*G)(s) = G(Z) = Γ_Z(G), including the usual terminal base-change iso.
  The second equation reads ρ ≫ (transported H⁰β) = this canonical identification.
  All other maps in this equation are isomorphisms, so it says precisely that
  transported H⁰β is inverse to ρ, followed by `(h_*G)(s) = G(Z)`. It also implies
  that ρ is an isomorphism. The inverse-germ clause is therefore fully included.
- The isomorphism and both identities cover unbounded E. Only G[0] in the final
  clause is concentrated in degree zero. No finiteness, torsion, properness, or
  boundedness condition is introduced.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.GeometricPointDerivedConstants`:
  `geometricPointConstants`, `geometricPointStalk`, `geometricPointConstantGerm`,
  `GeometricPointDerivedConstantsData`, `nonempty_geometricPointDerivedConstantsData`.
- `Mathlib.Algebra.Homology.Additive`: `Functor.mapHomologicalComplex` (the termwise
  constant functor), via the existing exact-functor derived construction.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection` and its
  `Derived.UpperLowerStar` dependency: `rightDerivedLowerStarProjectionMap`'s canonical
  `derivedUpperStarLowerStarAdjunction`, with `upperStar` and `lowerStar` from
  `UpperLowerStar.Defs`. The projection-map module is imported as the recorded interface;
  this item uses its adjunction, not the tensor-valued projection map.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`: `rightDerivedGlobalSections`.
- `Sheaf.AlgebraicGeometry.PullbackConstantModule`: `Scheme.pullback_constantModule_isIso`;
  its `WeilConjectures.ConstructibleSheaf.Defs` interface supplies the actual
  `Scheme.upperStarConstantSheafIso` descended by the module.
- `Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap`:
  `derivedConstantGlobalSectionsAdjunction`.
- `WeilConjectures.CategoryTheory.DerivedCategory.Adjunction`:
  `Adjunction.mapDerivedCategoryAdjunction`.
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory`:
  `Functor.leftDerivedFunctorIsoMapDerivedCategory`.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategoryNatIso`, `Functor.mapDerivedCategoryCompIso`, and
  `Functor.mapDerivedCategoryHomologyFunctorIso`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`:
  `Functor.homologyRightDerivedFunctorObjSingleFunctorIso`; Mathlib's
  `CategoryTheory.Abelian.RightDerived`: `Functor.rightDerivedZeroIsoSelf`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections`:
  `lowerStarCompGlobalSectionsIso`; `Mathlib.CategoryTheory.Sites.GlobalSections`:
  `Sheaf.Γ`, `Sheaf.ΓNatIsoSheafSections`;
  `Mathlib.CategoryTheory.Sites.Point.Basic`: `Point.toPresheafFiber`.
- The proof imports also retain the recorded K-injective existence, homotopy-adjunction,
  preservation of K-injectives, K-injective Hom/localization, enough-injectives,
  nonnegative injective-resolution, and right-adjoint-limits interfaces. All seven
  natural-language proof steps, with their node citations, are in the theorem docstring.

Sources opened: sites-cohomology.tex `lemma-adjoint` (07A6) and the following
`lemma-derived-pushforward-composition`; etale-cohomology.tex
`lemma-equivalence-abelian-sheaves-point` (04JQ) and
`lemma-projection-formula-proper` (0F0F). The latter uses the geometric-fibre sections
reduction; the former supplies the unbounded adjunction used in the node's proof.

Edge cases checked before writing: Z empty (all source sheaves and derived sections zero),
G zero, E zero, h the identity on Spec Ω, arbitrary characteristic of Ω, nonproper h,
non-torsion G, and unbounded E. In particular the degree-zero assertion does not claim
that Γ_Z or h_* is exact: only their zeroth right-derived functors are identified by
left exactness. For identity h, the normalization reduces to stalk/global-sections
identification inverse to the ordinary germ. Every displayed arrow has the required
source and target, and the traversed order of γ and both counits was checked explicitly.

Searches (all through the prescribed wrapper or read-only rg):

- `msearch.py … leanfinder`: “Geometric stalk of derived pushforward to an algebraically
  closed point equals derived global sections compatibly with adjunction counits”:
  eight hits, all about structure-sheaf Zariski stalks; none is this theorem.
- `msearch.py … loogle`: `"rightAdjointUniq", "counit"`: four hits, including
  `Adjunction.rightAdjointUniq_hom_app_counit`. These are the generic categorical tool,
  not the geometric comparison with degree-zero normalization.
- `msearch.py … grep`: `rightAdjointUniq|rightDerived.*[Ss]talk|[Ss]talk.*rightDerived`
  under CategoryTheory: nineteen hits for uniqueness of right adjoints and unrelated
  uses; no geometric theorem.
- `msearch.py … leansearch`: “Derived direct image to a geometric point is derived
  global sections, with the canonical counit and inverse germ normalization”:
  eight hits about topological and structure-sheaf germs; no matching declaration.
- Read-only `rg` in upstream WeilConjectures for sections/stalk, derived global sections,
  and the exact item id: found Leray's `rightDerivedLowerStarCompRightDerivedGlobalSectionsIso`
  and ordinary `lowerStarCompGlobalSectionsIso`, but neither identifies the geometric
  stalk or proves the two required normalizations; no exact item declaration exists.
- Read-only `rg` in project `lean/Sheaf` for the same concepts found the normalized
  geometric-point dependency and unrelated local sections comparisons, but no theorem
  covering this item. Searches for every new `geometricPointSections…` helper name and
  `geometricPointDerivedSectionsIso` in upstream, the project, and
  `dag/lean_names_upstream.json` found no collisions.

Validation: every delivered Lean declaration is compiled together as this one module,
using only `scompile.py` and its private overlay. The final delivery dry run and compile
results are recorded below after completion.

Compilation results: `scompile.py NO lem-kun-geometric-point-derived-sections-adjunction`
passed for both its sandbox pass (14.4 s) and the final module-name pass (17.4 s), with
no compiler errors or warnings. The only initial mismatch was the chosen terminal
object versus the explicit identity neighbourhood in the germ map; this was repaired
by using `MorphismProperty.Over.mkIdTerminal` for precisely that neighbourhood. The
final signature matches `lean.statement` verbatim, all Lean lines have at most 100
characters, and the file contains exactly the one intended theorem `sorry`.

The required `deliver2.py NO lem-kun-geometric-point-derived-sections-adjunction --no-push`
completed with `OK (dry run)`: server preflight and compilation both passed. The delivery
changes exactly the one module, the item's `lean` record, and this worker report. The
maintainer performs the independent review under the current direct-delivery workflow.

## Second reading by NO

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
