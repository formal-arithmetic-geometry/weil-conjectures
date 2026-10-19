## Worker report

Delivery: `Sheaf.Paper.NearbyProperHyperdescent`, declaration
`AlgebraicGeometry.Orgogozo.universalTruncatedComparison_of_proper_hypercover`.
This states the node, with one `sorry` and no new definitions or auxiliary postponed theorems.
The node changes only in `lean` and the addition of the already recorded
`lem-weil-pbc-matching-object-proper-faces` to `stmt_deps`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A Noetherian base S is `[IsLocallyNoetherian S] [CompactSpace S]`, exactly the two
  components of Mathlib's `IsNoetherian`. There is no integrality or reducedness assumption.
- The schemes are `{X S : Scheme.{u}}`, and the proper map is `(f : X ⟶ S) [IsProper f]`.
- The finite commutative coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  This is the common small-etale coefficient size of the recorded constructibility predicate;
  the intrinsic coefficient ring is its canonical `Coeff Λ = ULift Λ`, not a different ring.
  Finite rings admit representatives in this size. The same convention is used by the
  published good-modification consumer.
- An integer annihilator is expressed by `(m : ℕ)`, `hm : 1 ≤ m`, and
  `hmΛ : ∀ x : Λ, m • x = 0`. Negative nonzero integer annihilators are equivalently
  represented by their positive absolute values. Invertibility on S is
  `hmS : IsUnit (m : Γ(S, ⊤))`.
- The bounded-above and nonnegative derived complex is `K`, the subtype of `EtaleDerived`
  satisfying the recorded `IsBounded`, together with
  `hKge : DerivedCategory.TStructure.t.IsGE K.val 0`. Boundedness plus nonnegativity is
  equivalent to the node's bounded-above nonnegative condition.
- Constructible cohomology is `hKc`, for every integer q. It asks for a sheaf F with
  `Scheme.IsConstructibleEtaleModuleSheaf F` and a module-linear natural isomorphism from
  the intrinsic q-th cohomology presheaf to the presheaf of F transported through
  `AsSmall.down`. The displayed restriction of scalars is along the actual sheafification
  unit `toSheafify`, composed with `forget₂ CommRingCat RingCat`; it keeps sections and
  restrictions, and fixes the coefficient action. There is no replacement by arbitrary
  additive-group isomorphisms. This is the inline existing presheaf functor construction,
  not a new definition of constructibility.
- The augmented simplicial scheme is `(U : SimplicialObject (Over X))`. Its nth term is
  `(U.obj (op (SimplexCategory.mk n))).left`, with augmentation the object's `.hom`.
  The functor laws in `Over X` give all simplicial and augmentation compatibilities.
- The matching scheme in each degree is the point of `M n`, a cone on the recorded
  `properFaceDiagram U n`; `hM n : IsLimit (M n)` gives its exact universal property.
  The arrow `μ n` is canonical because `hμ` requires its projection along every proper
  face a to be `U.map a.obj.hom.op`. This uniquely determines the arrow by `hM`.
  Choosing arbitrary limiting cones merely avoids fixing a noncanonical model.
- The proper-surjective matching conditions, including degree zero, are `hproper` and
  `hsurj` for every natural n. The degree-zero diagram is empty, so its limit in `Over X`
  is X and the degree-zero matching arrow is the augmentation up to its unique isomorphism.
  For n+1 this is exactly the matching scheme `(cosk_n^X U)_(n+1)` in the node.
- Each term is finite type over S by `hft n`, the conjunction of `LocallyOfFiniteType`
  and `QuasiCompact` on its augmentation followed by f. No extra properness of a component
  augmentation is assumed separately.
- `f_i` is literally `(U.obj (op (SimplexCategory.mk i))).hom ≫ f`.
  `K_i` is literally the object obtained by applying the recorded
  `(etaleModules ε_i).pull (Coeff Λ)` to `K.val`. Its subtype proof is the existing
  `Functor.bounded_mapDerivedCategory_obj K.property` applied to the exact
  `(etaleModules ε_i).modulePull (Coeff Λ)`; there is no additional boundedness hypothesis
  and no new theorem claiming this fact.
- The truncation parameter is `(r : ℤ) (hr : -1 ≤ r)`.
  `hlevels : ∀ i : ℕ, (i : ℤ) ≤ r + 1 → ... (r - (i : ℤ))` is exactly
  `P_(r-i)(f_i,K_i)` for `0 ≤ i ≤ r+1`.
- The conclusion is exactly `UniversalTruncatedComparison f Λ K r`. Unfolding the
  recorded definition retains both arbitrary base-change quantifiers and the inclusive
  cohomology bound `i ≤ r` for the ordinary comparison cone.

Dependency declarations read and used:

- `Sheaf.Paper.OrgogozoInductionData`: `AlgebraicGeometry.Orgogozo.UniversalTruncatedComparison`
  and its `ConeVanishesThrough`. Full definitions and docstrings read.
- `Sheaf.Paper.OrientedNearbyCycles`, publicly imported through the preceding module:
  `EtaleSite`, `etaleTopology`, `etaleDatum`, `Coeff`, `EtaleDerived`, `IsBounded`,
  `etaleModules`, and the underlying ordinary comparison used by P. Their signatures
  and definitions were read in the published file.
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`, with the full finite
  locally closed stratification and finite-value module trivialization definition read.
- `Sheaf.CategoryTheory.ProperFaceMatchingObject`:
  `CategoryTheory.SimplicialObject.properFaceDiagram` and `ProperFaceCategory`;
  the node's two matching-object theorem statements and docstrings were also read.
- Mathlib `AlgebraicGeometry.IsProper`, `LocallyOfFiniteType`, `QuasiCompact`,
  `IsLocallyNoetherian`, `CategoryTheory.Limits.pullback`, and `DerivedCategory`, from the
  exact recorded Mathlib modules. All signatures and surrounding docstrings read.
  These imports are supplied publicly by the recorded statement dependencies.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.bounded_mapDerivedCategory_obj`, publicly available from
  `OrientedNearbyCycles`; its exact boundedness statement and exact-functor assumptions read.
- Proof-only import `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`,
  with `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`
  read. This is the recorded `prop-pur-kinjective-resolutions-exist`.

The other proof-only nodes (general-nearby-slice-test, proper-hypercover-etale-descent,
 simplicial-derived-image-spectral-sequence, simplicial-proper-exchange, and
 dplus-injective-representative) have no recorded Lean modules on the read base;
there are no imports to add for them yet. Their proof steps remain explicitly named
in the theorem docstring. They are proof inputs, not missing notions of this statement.

The helpers `orgogozoConstantScalars` and `orgogozoModuleSections` were inspected in
`Sheaf.Paper.OrgogozoGoodModification`. Importing that module would create the reverse
edge to this theorem's own consumer. Instead the theorem displays their existing
underlying Mathlib functor expressions directly and introduces no duplicate declaration.

Edge cases checked: r=-1 demands precisely i=0 and `P_(-1)`; r=0 demands i=0,1;
all negative comparison degrees are retained. At matching degree zero the empty
proper-face diagram gives the base X; degree one gives `U_0 ×_X U_0` with two unrestricted
vertex components. Empty schemes and zero complexes are permitted. A zero coefficient
ring and m=1 are permitted; no nontriviality or characteristic hypothesis was inserted.
Neither base-change quantifier in P restricts T or T' to Noetherian schemes.
The complex's bounds are cohomological, not bounds on a selected chain representative.

Searches made using the prescribed wrapper:

- LeanFinder: `Proper hypercover descent for universal truncated nearby cycle base change`.
  Eight results, concerning one-step hypercover preservation/locality; no matching theorem.
- Loogle: `"nearby"`. Only `Units.ofNearby` and `Units.val_ofNearby`; unrelated.
- grep: `nearby.*hyper|properHypercover|Milnor.*descent`. Zero Mathlib hits.
- LeanSearch: `Proper hypercover descent for truncated nearby cycles`. Eight one-step
  hypercover/locality results; no nearby-cycle theorem.
- `rg` with the same expression in the named upstream `WeilConjectures` directory and
  `lean/Sheaf`: only the good-modification proof docstring cites this node.
- `grep -rn` of the exact node id in the named upstream source: no hits.
- DAG and module searches for matching-object interfaces found the already recorded
  proper-face diagram. Its generic category parameter specializes to `Over X` without
  an interface repair. No new definition node is needed.

Source verification: read Orgogozo's author PDF at the node's URL, §3.1 and
Lemmas 3.1.1--3.1.2, printed pp. 6--7. The nonconstant torsion variant is explicitly
stated there. The source and current DAG agree on the universal version and on the
finite diagonal using indices through r+1. No statement correction or disputed claim.

Validation: prescribed `scompile.py Q27 lem-trf-nearby-proper-hyperdescent
lean/Sheaf/Paper/NearbyProperHyperdescent.lean` compiled the sandbox and library-file
forms successfully (4.2 s and 3.7 s), with no diagnostics. Every variable and universe
is explicit, all lines are at most 100 characters, and the only proof is `by sorry`.

## Second reading by Q27

A separate second pass by the same dispatched worker re-opened the node and the
completed Lean statement; the dispatch brief forbids starting another agent, and the
maintainer supplies the independent review after delivery. This pass checked every
correspondence listed above, in particular: the actual `.left` morphisms carry
properness and surjectivity; `.hom ≫ f` is the finite-type map to S; the matching-map
projection equations fix μ rather than assuming arbitrary cover maps; the hKc
isomorphism is module-linear; and the P hypothesis uses r-i with both base-change
quantifiers, not a comparison only over S. The hlevels subtype has exactly the pulled
back object and an existing exact-pullback boundedness proof. No mismatch or file
change was needed after the clean compile. No extra assumptions on strata, reducedness,
Noetherian base changes, or component-complex bounds were introduced.
