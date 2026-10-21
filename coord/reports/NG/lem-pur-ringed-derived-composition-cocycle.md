## Worker report

The module `Sheaf.CategoryTheory.RingedDerivedCompositionCocycle` states the item in
`CategoryTheory.ringedDerivedComposition_cocycle` and
`CategoryTheory.ringedDerivedComposition_units`. Both proofs are `by sorry`.
There are no new definitions, new nodes, dependency repairs, or statement corrections.
The node's non-Lean fields are unchanged. No statement dispute was found.

The source read was `literature/stacks-project/sites-cohomology.tex`, lines 4011–4030,
lemma-derived-pushforward-composition, Tag 0D6E. That lemma supplies composition;
the present node supplies its coherence, with the eight-step common-resolution proof
already recorded in the DAG. Each theorem's docstring carries its part of that proof.
The example Sheaf compact-object module is withdrawn; its recorded upstream replacement
`WeilConjectures.CategoryTheory.CompactObject` was read for the header conventions.
No repair note exists for this item.

### Hypotheses and clauses

- Small ringed sites X0, X1, X2, X3: the first theorem binds `C0` through `C3 : Type u`,
  each with `SmallCategory`, and `J0` through `J3 : GrothendieckTopology Ci`.
  Each `Ai : Sheaf Ji CommRingCat.{u}` is exactly the sheaf of commutative rings.
  Commutativity is forgotten only when passing to the recorded ringed-topos/module
  interfaces. The second theorem independently quantifies the two sites of an arbitrary f.
- Geometric morphisms, structural maps and their induced module direct images:
  `f`, `g`, `h : RingedToposMorphism ...`, at successive sites. That existing structure
  includes the sheaf adjunction, finite-limit preservation, structural ring map and its
  identities, and the induced additive module direct image with its coefficient action.
  It does not require a presenting-site functor. We do not replace it by an abstract
  additive functor.
- Ordinary unbounded module derived categories: every corner is
  `DerivedCategory.{w} (ringedSiteModules.{u,u,u,u} ...)`, with
  `[HasDerivedCategory.{w} ...]` at that corner. Complexes are indexed by all of `ℤ`.
  These binders select the localization and its morphism-size universe, as in the
  recorded composition theorem, and do not impose a mathematical finiteness condition.
- Rf, Rg, Rh, R(gf), R(hg), R(hgf): the six functor binders `Rf`, `Rg`, `Rh`,
  `Rgf`, `Rhg`, `Rhgf` have exactly the corresponding source and target derived
  categories. Their `ηf`, `ηg`, `ηh`, `ηgf`, `ηhg`, `ηhgf` binders and
  `IsRightDerivedFunctor` instances say they are total right derived direct images.
  For composites the ordinary direct image is the composite of the module functors,
  exactly the convention used by the recorded dependency. Parenthesizing the triple
  composite does not change its termwise functor.
- The specified K-injective normalized κ: `κgf`, `κhg`, `κh_gf`, `κhg_f` are natural
  isomorphisms in precisely the stated directions. `hκgf`, `hκhg`, `hκh_gf`, and
  `hκhg_f` are **verbatim in form the first unit equation inside the unique-existence
  clause of `ringedToposDerivedPushforwardComposition`**:
  `ηgf.app M ≫ κgf.hom.app (Q.obj M) = ηg.app (f_* M) ≫ Rg.map (ηf.app M)`.
  That theorem's uniqueness clause characterizes κ by this equation, and its final
  clause identifies the same κ with the K-injective normalization. Thus these binders
  unpack “let κ be the normalized comparison”; they do not add a new geometric
  assumption. Universal uniqueness also transports this characterization to any
  representatives of the derived pairs. We do not bind arbitrary unconstrained κ.
- Cocycle conclusion: Lean composition runs left to right. The displayed conclusion
  starts with `κh_gf.hom`, then `Functor.whiskerRight κgf.hom Rh`, then
  `(Functor.associator Rf Rg Rh).hom`. Its other side is `κhg_f.hom` followed by
  `Functor.whiskerLeft Rf κhg.hom`. Both start at `Rhgf` and end at
  `Rf ⋙ (Rg ⋙ Rh)`. This is exactly the node's equation with its suppressed
  associator restored, not a componentwise weakened version.
- Identity direct images: in `ringedDerivedComposition_units`, `R0`, `R1` are total
  derived functors of the identity direct images. After the termwise identity
  identification their units are `η0 : Q ⟶ Q ⋙ R0` and `η1 : Q ⟶ Q ⋙ R1`.
  The `IsRightDerivedFunctor` instances use the actual quasi-isomorphisms on each
  module-complex category. This writes the ordinary identity functor explicitly by
  its action Q, rather than choosing an unrelated identity lift.
- Comparisons with identities: `κleft : Rf ≅ Rf ⋙ R1` and
  `κright : Rf ≅ R0 ⋙ Rf` have the ordinary identity compositions already identified
  with f by the ordinary functor unitors. `hκleft` and `hκright` are the same
  normalized unit characterization as above in these coordinates.
- Identity comparisons induced by termwise identity direct image: the existential
  `ε0 : R0 ≅ 𝟭 _`, `ε1 : R1 ≅ 𝟭 _` is accompanied, for **every** complex M, by
  `ηi.app M ≫ εi.hom.app (Q.obj M) = 𝟙 _`. This specifies the canonical maps induced
  by the termwise identity. It is not a bare existence claim about arbitrary isos.
  The universal property determines these normalized comparisons uniquely.
- Left unit law: the third conjunct is
  `κleft.hom ≫ Functor.whiskerLeft Rf ε1.hom ≫ (Functor.rightUnitor Rf).hom = 𝟙 Rf`.
  Right unit law: the fourth conjunct uses `κright`, `Functor.whiskerRight ε0.hom Rf`
  and `Functor.leftUnitor Rf`. The explicit unitors restore the suppressed functor
  unit identifications. These are equalities of natural transformations.
- Coefficient changes on the identity underlying topos: the quantified geometric
  inverse/direct functors may be identities while the structural ring maps are
  arbitrary. No injectivity, flatness or invertibility of these maps, and no
  preservation of K-injectives by direct image, occurs anywhere. Thus all such
  cases and mixtures are included in the same universal statements.

### Dependency declarations read and used

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q` and its localization instance. These
  give the ordinary unbounded localization in both declarations.
- `Sheaf.CategoryTheory.RingedToposMorphism`:
  `CategoryTheory.RingedToposMorphism`, including its full generalized-element
  ring-map/module-linearity fields, `modules` and its additive instance.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, the transparent abbreviation for Mathlib's
  `SheafOfModules`. Mathlib's underlying structure and linear morphisms were read too.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`:
  `CategoryTheory.ringedToposDerivedPushforwardComposition`. Its full signature and
  proof-plan docstring were read: existential universal derived pairs, invertible
  units on K-injectives, and the uniquely characterized κ with both the unit
  equation and arbitrary-intermediate-resolution normalization. It is publicly
  imported and supplies precisely the comparison used by the item.
- Proof import `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`:
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`.
- Proof imports `Mathlib.Algebra.Homology.DerivedCategory.KInjective` and `.Plus`:
  `CochainComplex.IsKInjective.Qh_map_bijective`, `.quasiIso_iff`, and the bounded-below
  specialization, as specified by the Hom dependency's Mathlib match.
- Proof import `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`:
  `CategoryTheory.Functor.kInjectiveDerivedMapComputation` and its functoriality,
  resolution-transition computation, laws and naturality declarations. The recorded
  `RightDerivedFunctorOfQuasiIsoResolutions` construction and unit signatures were
  also read to verify their resolution-coordinate conventions.

### Edge cases

Checked mathematically before writing: zero complexes and the zero coefficient ring;
all three morphisms identities, or an identity in any single position; empty presented
sites; arbitrary structural maps such as ℤ→ℤ/2 on the identity underlying topos;
mixtures of coefficient restrictions and genuine geometric direct images. The formulas
use no nonzero object, points, nonempty objects or invertible coefficient map. All
complex degrees are integers. The arbitrary universes u and w match the small-site
interface of the dependencies; no new equality between independent site universes
is imposed beyond that interface. The two units are treated for every complex, not
only for K-injectives or for a fixed preferred resolution.

### Searches

All msearch calls used group NG and this item. Their local search log is generated
by the wrapper. No exact existing declaration was found.

- `leanfinder`: “K-injective normalized derived pushforward composition associativity
  and identity coherence for ringed topoi”: eight hits, headed by
  `SheafOfModules.pushforward_assoc`, `pushforwardComp`, and `pushforward_id_comp`.
  The candidate source `Mathlib/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean`
  was read at its composition/unit declarations. These concern underived pushforward
  along presenting-site functors, not unbounded derived geometric direct images.
- `loogle`: “CategoryTheory.Functor.rightDerivedUnique,
  CategoryTheory.Functor.rightDerived_ext”: no hits for the combined query. The actual
  source `Mathlib/CategoryTheory/Functor/Derived/RightDerived.lean` was read, including
  `IsRightDerivedFunctor`, `rightDerivedDesc`, `rightDerived_ext`, `rightDerivedNatTrans`,
  `rightDerivedNatIso` and `rightDerivedUnique`. These give general universal-property
  tools, not the ringed-topos composition/identity laws being stated.
- `grep` via msearch, subdirectory CategoryTheory:
  `rightDerived.*[Cc]omp|[Cc]omp.*rightDerived|rightDerived.*[Aa]ssoc`: 18 hits in
  general derived-functor/adjunction APIs and the bounded-below classical right-derived
  functor API. None states these laws for the normalized total direct-image comparison.
- `leansearch`: “The normalized comparison of unbounded right derived direct images
  satisfies associativity and identity coherence”: eight hits, including
  `NatTrans.rightDerived_comp_assoc`, `Functor.rightDerived_fac_assoc`, and
  `Functor.rightDerivedNatTrans_comp_assoc`. The first is functoriality in natural
  transformations for the classical degreewise right-derived functors; the others
  are universal factorization/natural-transformation functoriality. None is this
  composition comparison between different unbounded module-derived categories.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for `RingedToposMorphism`,
  `ringedToposDerived`, and `normalizedDerivedComparison` located the used composition
  theorem and the normalized comparison family. Those other comparisons involve
  exact change functors and differ from the present non-exact direct-image composite.
  `RingedDerivedComparisonData` and `RingedDerivedMonoidalComparisons` were read:
  their interfaces additionally require chosen tensor/adjunction lift data and do
  not assert this standalone cocycle/unit statement for ordinary ringed-topos
  direct images. No part of that stronger interface is assumed here.
- `rg` for the item id in `lean/WeilConjectures` found no attachment. Exact-name
  searches for both new declarations in `dag/lean_names_upstream.json`, Mathlib,
  `lean/WeilConjectures` and `lean/Sheaf` found no existing declaration.

### Validation

`scompile.py NG lem-pur-ringed-derived-composition-cocycle` compiled this module on
both the server sandbox pass and the library pass, each clean (12.7 s and 12.4 s).
After adding direct dependency imports and the main-statements module list, the
required delivery dry run recompiles the final source and runs server preflight.
All variables and universes are bound explicitly; `autoImplicit` is false. Every
line is at most 100 characters. Both theorem proofs are only `sorry`.

## Second reading by NG

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
