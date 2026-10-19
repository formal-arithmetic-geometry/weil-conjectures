## Worker report

`lean/Sheaf/SixFunctors/ConnectedEtalePerfectConstant.lean` states
`AlgebraicGeometry.Etale.connected_etale_perfect_constant`. Its only theorem proof is
`sorry`. Its canonical helper `AlgebraicGeometry.Etale.geometricStalk` has real data:
it applies `mapDerivedCategory` to the recorded exact geometric `sheafFiber`, using
the existing `sheafFiber_additive` instance. It introduces no alternative stalk construction.

The statement matches each hypothesis and conclusion as follows:

- The arbitrary commutative Noetherian ring is `R : Type (u + 1)` with `[CommRing R]`
  and `[IsNoetherianRing R]`. There is no `Finite R` or finite-set condition.
- The nonempty connected scheme is `X : Scheme.{u}`, `[Nonempty X]`, `[ConnectedSpace X]`.
- `L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))` is the
  unbounded derived category of constant-coefficient module sheaves. The fixed-scalar
  ModuleCat-valued encoding is the standard realization of modules over the constant ring.
- `hbounded` asserts vanishing of every cohomology object outside some integer interval.
  The name `homologyFunctor` on cochain complexes denotes the degree-q cohomology object.
- In `hlisse`, each cohomology sheaf satisfies the published `IsLocallyConstantSheaf`;
  its fibre at every geometric point is `Module.Finite R`. Local constancy and these
  stalk conditions say precisely that the locally constant module values are finitely
  generated. Algebraically closed fields `Ω : Type u` and `x : Spec (.of Ω) ⟶ X`
  encode geometric points, with enough such points in this universe.
- `hTor` supplies `a b : ℤ`, `a ≤ b`, and vanishing outside `[a,b]` after tensoring
  with every sheaf `F` in degree zero. The published `Etale.derivedTensor` is the
  canonical derived tensor on the ModuleCat-valued realization; `singleFunctor ... 0`
  places exactly `F` in degree zero. No constructibility or finiteness condition is put on F.
- `E : DerivedCategory (ModuleCat R)` and `IsPerfectRingComplex E` mean that E has
  a bounded finite-projective module representative, using the dependency's predicate
  with an independent localization universe.
- `𝒰 : Scheme.Cover Scheme.etalePrecoverage X` is the required jointly surjective
  étale family. For each index, `Nonempty (... ≅ ...)` asserts that the exact derived
  étale pullback of L is isomorphic to the constant derived E on that member.
- The next universal clause says `Nonempty (E ≅ (geometricStalk R x).obj L)` at
  every geometric point. E is outside the quantifier, so all stalks have the same value.
- The moreover clause quantifies over every `W : X.ProEt` with `[IsAffine W.left]`
  and `(ProEt.topology X).IsWeaklyContractible.{u + 1} W`. Membership in `X.ProEt`
  already includes weak étaleness, so there is no redundant hypothesis for it.
  The left side is comparison inverse image followed by exact derived pullback along
  `W.hom`; the right side is constant derived E on W's small pro-étale site. For a
  weakly étale object, this pullback is restriction to its slice, transported to W's
  small pro-étale site. There is no connectedness or nonemptiness assumption on W.

I read the source at Stacks `etale-cohomology.tex`, lemma-connected-ctf-locally-constant
(Tag 09BI): one finite-projective model is obtained by grouping local models by derived
isomorphism class and connectedness. The stalk conclusion follows from the same local
isomorphisms. I also read `proetale.tex`, lemma-connected-adic-lisse (Tag 09C6), at its
weakly contractible covering step, and the site's covering-splitting definition (090K).
The theorem docstring records the K-flat/unit reduction, bounded constant local models,
connectedness argument, stalk Tor comparison, perfect replacement, comparison/restriction,
finite affine refinement, disjoint coproduct and covering section argument, including empty W.

Dependency declarations read and used (module; declaration):

- `Mathlib.AlgebraicGeometry.Scheme`; `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.RingTheory.Noetherian.Defs`; `IsNoetherianRing`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`; `Scheme.smallEtaleTopology`, `Scheme.Etale`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`; `CategoryTheory.constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`; `CategoryTheory.ringedSiteModules`, the
  intrinsic ringed-site module interface (realized here by fixed-scalar sheaves).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`; `DerivedCategory` and its localization.
- `Mathlib.RingTheory.Finiteness.Defs`; `Module.Finite`.
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`;
  `SheafOfModules.wf_site_derived_tensor_descent` (canonical K-flat tensor interface).
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`;
  `DerivedCategory.IsPerfectRingComplex`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`; `IsAlgClosed`; geometric points use the
  recorded `Scheme.SpecToEquivOfField` convention.
- `Mathlib.CategoryTheory.Sites.Point.Basic`; `GrothendieckTopology.Point.sheafFiber`,
  and `Scheme.pointSmallEtale` from `Mathlib.AlgebraicGeometry.Sites.EtalePoint`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`; `Scheme.proEtaleDerivedCategory`:
  the small pro-étale site and intrinsic constant-ring realization. Here the equivalent
  fixed-scalar realization supports the published arbitrary-R geometric pullback API.
- `Sheaf.AlgebraicGeometry.ProEtaleSmallModelComparison`;
  `Scheme.smallModelProEtaleComparison`, which publicly retains the original geometric
  comparison. The statement uses that original `ProEtale.comparisonUpperStar` on modules.
- `WeilConjectures.CategoryTheory.Sites.WeaklyContractible`;
  `GrothendieckTopology.IsWeaklyContractible`: every locally surjective set-sheaf map
  is surjective on W-sections, equivalently every epimorphism is.

Additional APIs used directly are `Etale.derivedTensor` from
`WeilConjectures.SixFunctors.Etale.Derived.Coefficients`,
`Scheme.IsLocallyConstantSheaf` from `WeilConjectures.ConstructibleSheaf.Defs`,
`ProEtale.comparisonUpperStar` from `WeilConjectures.SixFunctors.ProEtale.Comparison.Defs`,
and `ProEtale.upperStar` from `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`.
All recorded statement modules are public imports, and every additional recorded proof
module is imported without `public`. No missing notion or dependency repair was needed.

Edge cases: the zero complex, zero ring, a one-degree Tor interval, arbitrary infinite
Noetherian coefficients, empty W, and disconnected W all remain included. For empty W the
restriction category is zero. For disconnected W a section of the disjoint affine covering
is used; no single-member lift is assumed. Empty X is excluded exactly by the node.
An interval with reversed endpoints in `hbounded` merely forces all cohomology to vanish;
`hTor` retains the explicit ordered interval. Site objects have universe u+1 and morphisms u;
modules and the set sheaves tested by weak contractibility live in u+1. No equality of the
site object and morphism universes is imposed.

Searches for existing declarations (fresh searches on 2026-10-17, with inherited detailed
search output retained in searches.jsonl):

- `msearch.py leanfinder`: “A connected scheme with a bounded locally constant complex
  of finite type modules and finite Tor amplitude has a single perfect constant etale
  local model”. Eight hits: Scheme.Etale and ordinary etale/ring-locality results; no match.
- `msearch.py loogle`: `CategoryTheory.Sheaf, CategoryTheory.Projective`. Nine hits
  concerning coherent/extensive sheaf comparison on projective sites; no derived assertion.
- `msearch.py grep`: `locallyConstant.*[Pp]erfect|[Pp]erfect.*locallyConstant|connected.*ctf`.
  Zero hits.
- `msearch.py leansearch`: “A bounded locally constant etale complex of finitely generated
  modules with finite Tor dimension has one perfect constant local model on a connected
  scheme”. Eight unrelated rank, condensed/discrete, and etale declarations; no match.
- Direct rg in `WeilConjectures/` and `lean/Sheaf` for connected/perfect, geometricStalk,
  derivedStalk and constantDerivedEtale, plus grep for this node id in WeilConjectures.
  No matching theorem or existing `Etale.geometricStalk` definition. The existing
  `Scheme.constantDerivedEtale` is an abbreviation of the same exact constantSheaf
  mapDerivedCategory expression used directly here, so no second constant construction
  is declared. Existing derived-stalk results concern conservativity, not this theorem.

No statement correction or STATEMENT-DISPUTED flag. The natural statement and all
non-lean node fields are unchanged. The signature is copied verbatim from the final file.
All variables and universes are explicit (`autoImplicit false`); every Lean line is at most
100 characters. scompile.py compiled the revised module in sandbox and library contexts
without errors or warnings. The required delivery dry run is the final validation step;
the independent second reader will add their own reading and deliver.

## Second reading by Q37

I read the node statement, its Stacks source places (09BI, 09C6, and 090K), every
recorded statement dependency, and the final Lean file independently. The item-by-item
rendering is:

- Objects: `R : Type (u + 1)` with `[CommRing R] [IsNoetherianRing R]`; `X : Scheme.{u}`
  with `[Nonempty X] [ConnectedSpace X]`; and `L` in
  `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))`. These are exactly
  the commutative Noetherian coefficient ring, nonempty connected scheme, and derived
  étale module complex in the node.
- Boundedness: `hbounded : ∃ a b : ℤ, ∀ q, q < a ∨ b < q →
  IsZero (homologyFunctor ... q).obj L`. This is precisely bounded cohomology; no
  finiteness or ordering hypothesis absent from the node is added.
- Lisse finite values: `hlisse` gives `IsLocallyConstantSheaf` for each cohomology
  object and, for every algebraically closed field `Ω : Type u` and geometric point
  `x : Spec (.of Ω) ⟶ X`, `Module.Finite R` of its `pointSmallEtale x` fibre. This
  matches locally constant finitely generated module values and the recorded geometric
  point convention.
- Tor amplitude: `hTor` introduces `a b : ℤ` with `a ≤ b`, then quantifies every
  degree-zero sheaf `F` and degree `q`, asserting `IsZero` of the degree-q cohomology
  of `Etale.derivedTensor ... L` applied to `singleFunctor ... 0` of `F` outside
  `[a,b]`. This is exactly the node's derived tensor condition.
- Conclusion objects: `∃ E : DerivedCategory (ModuleCat R),
  IsPerfectRingComplex E ∧ ∃ 𝒰 : Scheme.Cover etalePrecoverage X`. The predicate is
  the recorded bounded finite-projective perfect-complex notion.
- Étale-local clause: for each `i : 𝒰.I₀`, `Nonempty` of an isomorphism between
  `Etale.upperStar ... (𝒰.f i)` applied to `L` and the derived constant sheaf of `E`
  on `𝒰.X i`. This renders `L|_{V_i} ≃ underline E|_{V_i}` and retains the cover.
- Geometric stalk clause: for every `Ω` and `x` as above,
  `Nonempty (E ≅ (geometricStalk R x).obj L)`. `geometricStalk` is the exact recorded
  `sheafFiber` mapped to derived categories; `E` is outside the quantifier as required.
- Pro-étale clause: for every `W : X.ProEt` with `[IsAffine W.left]`, an explicit
  `hW : (Scheme.ProEt.topology X).IsWeaklyContractible W` yields a `Nonempty`
  isomorphism from the comparison inverse image of `L`, pulled to `W`, to the derived
  constant `E` on `Scheme.ProEt.topology W.left`. This is the node's moreover clause;
  membership in `X.ProEt` supplies weak étaleness and no connectedness of `W` is added.

Edge cases checked: zero `L`, zero `R`, arbitrary infinite Noetherian `R`, a one-degree
Tor interval, empty `W`, disconnected `W`, and the empty scheme. The latter is excluded
only by `[Nonempty X]`, exactly as the node requires. Reversed bounds are harmless for
`hbounded` (they force vanishing), while `hTor` retains the required `a ≤ b`. The site
object/morphism universes remain `u + 1`/`u`; no universe equality or finite-set
assumption is imposed.

Searches were repeated with `msearch.py` LeanFinder, Loogle, LeanSearch, and grep over
Mathlib, `WeilConjectures/`, and `lean/Sheaf` for connected locally constant perfect
étale complexes, geometric stalk constructions, and constant derived étale objects.
Only unrelated étale, condensed, and generic stalk declarations were found. The existing
`Scheme.constantDerivedEtale` abbreviation is the same constant-sheaf
`mapDerivedCategory` expression and is not duplicated. No missing notion or unusable
dependency was found.

Mismatch audit: none. I changed no statement, hypothesis, conclusion, dependency, or
definition. The helper `geometricStalk` has real data and uses the existing exact fibre
functor; it is not hollow. The theorem proof is the single permitted `sorry`, with its
source and `(blueprint: lem-sfb-connected-etale-perfect-constant)` proof plan in the
docstring. `scompile.py` passed both sandbox and library compilation.
