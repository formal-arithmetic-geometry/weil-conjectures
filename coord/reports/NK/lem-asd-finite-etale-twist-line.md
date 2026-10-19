## Worker report

The item is stated by
`AlgebraicGeometry.Scheme.finite_etale_torsion_twist_line` in
`Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`. Its statement is unchanged.
The additional definition module constructs the nonnegative finite torsion twists;
its data contain no `sorry`. The result and the three named construction-law
lemmas have `sorry` proofs, with sources and full proof outlines in their docstrings.
No proof is supplied at this stage.

Hypothesis and clause comparison:

| Node text | Lean rendering |
| --- | --- |
| T is an arbitrary scheme | `(T : Scheme.{u})` |
| N is an integer at least 1 | `(N : ℕ) (hN : 0 < N)`; precisely the positive integers |
| N invertible in every local ring | `hInvertible : ∀ t : T, IsUnit (N : T.presheaf.stalk t)` |
| A is a finite commutative ring | `(A : Type (u + 1)) [CommRing A] [Finite A]` |
| NA = 0 | `hA : (N : A) = 0`; equivalence follows by taking a = 1 in NA = 0 and, conversely, multiplying the cast equality by any a |
| Small ordinary étale site | `T.smallEtaleTopology` on `T.Etale` throughout |
| Constant coefficient sheaves | `constantSheaf` with `ModuleCat.of A A`, and the canonical constant scalar extension from `ZMod N` |
| μ_N(U) consists of Nth roots of units | existing `T.rootsOfUnitySheaf N`, the kernel of `N • 𝟙 T.gmSheaf` |
| The action a · z = z^a | `AddCommGroup.zmodModule (finiteEtaleMu_annihilated T N U)` on the existing additive encoding of the multiplicative group; `toZModLinearMap` retains the original restriction maps |
| A_T(1) = μ_N tensor A | `finiteEtaleTateLine`: sheafification of `finiteEtaleMuModulePresheaf ⋙ ModuleCat.extendScalars (finiteEtaleTwistScalar N A hA)` |
| A_T(0) = A_T | the zero branch of `finiteEtaleTateTwist`, literally the constant sheaf on the regular A-module |
| Positive twists are tensor powers | degree 1 is `finiteEtaleTateLine`; degree r+2 is degree r+1 tensor the same line, with `Sheaf.monoidalCategory` |
| For each r >= 0 | `(r : ℕ)`, with no further condition |
| There is an étale covering of T | `∃ cover : Cover.{u} etalePrecoverage T` |
| On every covering member the twist is A with its module action | the `Nonempty` isomorphism between `(finiteEtaleTateTwist ... r).over (cover.etalePrecoverageToEtale i)` and `constantSheaf` of `ModuleCat.of A A` on the localized site |
| Locally constant | `IsLocallyConstantSheaf (finiteEtaleTateTwist ... r)` |
| Locally free of rank one | exactly the displayed local isomorphisms of A-module sheaves to the regular module A, rather than just isomorphisms of underlying sets or groups |
| Flat, tensoring preserves exact sequences | `PreservesFiniteLimits` and `PreservesFiniteColimits` of the canonical `MonoidalCategory.tensorLeft` by the twist |

The last pair is the usual exact-functor formulation in this abelian category:
an additive functor preserves finite limits and finite colimits precisely when it
preserves short exact sequences. Preservation of arbitrary exact sequences follows
by factoring through images. The tensor functor is additive. No preservation of
infinite products or infinite limits is asserted.

The module-valued encoding is the established ordinary-étale convention. Its
identification with modules over the constant ring sheaf is the recorded
`etaleConstantModuleFunctor_isEquivalence` in
`Sheaf.AlgebraicGeometry.EtaleConstantRingModuleEquivalence`: extension of the
constant scalar action leaves the underlying abelian presheaf unchanged; its
explicit inverse restricts the scalar action. Thus the local isomorphisms are
module isomorphisms over A_T, not merely abelian-sheaf trivializations. Constant
coefficient sections of A_T are locally constant elements of A. Consequently
balancing section tensors over A_T is locally the same balancing as over A;
sheafification identifies the canonical tensor in the two encodings. The tensor
is Mathlib's existing `Sheaf.monoidalCategory`, the sheafification of the tensor
presheaf. The ringed-site tensor and scalar-extension declarations recorded by
`def-pur-sheaf-tensor-product` are imported, and no replacement tensor product is
defined. The `positiveTensorPower` specialization in that dependency requires
the site and module universes to coincide. Here the site has object universe u+1
and hom universe u, so the same tensor-power recursion is made on module-valued
sheaves using the existing canonical sheaf tensor. This is a construction of the
new notion A_T(r), not a new definition of tensor products.

The first twist uses `ModuleCat.extendScalars`, whose convention places A in the
first factor: A tensor μ_N. Symmetry of the ordinary tensor product identifies
this with the node's μ_N tensor A, with its A-action. There is no flatness
hypothesis on A over ZMod N. The coefficient ring map is concretely
`ZMod.castHom ((CharP.cast_eq_zero_iff A (ringChar A) N).mp hA) A`;
no map or module sheaf is chosen from an undetermined existence theorem.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology` and
  `Scheme.Etale`; coverings are `Cover etalePrecoverage`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the transparent abbreviation for `SheafOfModules`; module-valued sheaves are
  identified with this exact category by the constant-ring module equivalence.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`:
  `SheafOfModules.monoidalCategory`, `changeOfRings`, `positiveTensorPower`;
  for constant coefficient module-valued sheaves, the same sheafified tensor is
  `CategoryTheory.Sheaf.monoidalCategory` from Mathlib's Sites/Monoidal.
- `WeilConjectures.ConstructibleSheaf.Defs`: `Scheme.LocallyConstantDatum`,
  `Scheme.IsLocallyConstantSheaf`, `Cover.etalePrecoverageToEtale`; localization
  uses the very `Sheaf.over` of this definition.
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`:
  `Scheme.rootsOfUnitySheaf` with its full general-scheme signature.
- `Sheaf.AlgebraicGeometry.EtaleConstantRingModuleEquivalence`:
  `etaleConstantModuleFunctor`, its inverse, and
  `etaleConstantModuleFunctor_isEquivalence`.

Every recorded stated proof dependency's module is imported. The unrecorded or
Mathlib proof inputs are covered by the imports of EtalePoint, MorphismProperty,
Morphisms/Etale, Point/Basic, Point/Skyscraper, and ShortComplex/ShortExact. The
full five-step proof from the node, including the named dependencies, is in the
main theorem's docstring.

Edge cases checked mathematically before writing:

- Empty T: stalk-unit hypothesis is vacuous; an empty covering is permitted and
  the sheaf category has its usual trivial objects. Nothing requires a point.
- Zero ring A: allowed by CommRing and Finite. All twists are zero as A-modules,
  including A itself; the free module on one generator remains the regular
  module A. No Nontrivial instance or cardinal-rank argument excludes it.
- N = 1: NA = 0 forces A to be the zero ring, so the same conclusion holds.
  The primitive-generator construction has an empty product equal to 1.
- r = 0: the definition is literally the regular constant sheaf, and the identity
  cover trivializes it. r = 1 is the scalar-extension object; later degrees are
  actual recursive tensors.
- Composite N and nonflat A over ZMod N: retained; the proof uses extension of
  the local isomorphism of μ_N, not preservation of arbitrary exact sequences
  by A tensor over ZMod N.
- Positive residue characteristics dividing N cannot satisfy the unit hypothesis.
  Characteristic zero and mixed characteristic bases satisfying it are included.
- Universe u is explicit. Coefficients and module carriers use u+1, as in the
  recorded ordinary-étale convention. Finite rings of any presentation can be
  placed there by universe lifting; no finite ring is excluded. Cover indices
  use the scheme universe u, in agreement with the recorded datum.

Searches (all performed before defining new notions):

- LeanFinder: “The sheaf of Nth roots of unity on the small etale site tensored
  with a finite ring killed by N has all nonnegative tensor powers locally
  constant free of rank one”: eight hits on condensed modules, none this result.
- LeanFinder: “Define nonnegative finite torsion Tate twist by scalar extension
  of the etale roots of unity sheaf and sheaf tensor powers”: eight hits on
  condensed tensors and general sheaf cohomology, no definition of this twist.
- Loogle: `"rootsOfUnity", "sheaf"`: no hits; `"rootsOfUnity"`: twelve hits on
  the algebraic subgroup and its elementary properties, no sheaf definition.
- LeanSearch: both “Finite torsion etale Tate twist sheaf defined by scalar
  extension of the roots of unity and nonnegative tensor powers” and “Sheaf of
  nth roots of unity on the small etale site as kernel of power map” failed
  with Internal Server Error. No mathematical inference was made from failure.
- msearch grep: `TateTwist|rootsOfUnity|roots.of.unity` in AlgebraicGeometry,
  and `finiteEtaleTateTwist|rootsOfUnitySheaf|TateTwist` throughout Mathlib:
  no hits.
- `rg` over upstream WeilConjectures and current lean/Sheaf found the existing
  Kummer roots sheaf, reused here; existing smooth twists are derived twisting
  data and Weil twists are l-adic Weil objects, rather than this construction.
- Upstream grep for the item id: no hit. Declaration-name searches in the
  upstream name index, Mathlib, WeilConjectures and lean/Sheaf: no collisions.
- DAG search and `tools/blueprint_refs.py search 'roots of unity'`: only the
  pro-étale sheaf, field group schemes and algebraically closed field
  trivialization, not the general ordinary-étale roots-of-unity definition.
  Blueprint search for “finite torsion Tate” gave no hits. All tool output is
  recorded in sandbox searches.jsonl; the new node records retain the queries,
  returned names and failures.

No statement correction or statement dispute was needed. There are no dependency
repair modules. All compilation was server-only through scompile.py, at nice 19,
two threads, and a 60-second per-file limit.

## New nodes

`def-asd-etale-roots-of-unity` records the exact existing declaration
`AlgebraicGeometry.Scheme.rootsOfUnitySheaf` from
`WeilConjectures.AlgebraicGeometry.Sites.Kummer` with `existing: true`, branch
slopmaster2. Its source is Section 03PK and Example 040M. It contributes no Lean
module and introduces no second sheaf. Existing DAG notions refer to a different
site or to schemes over special fields. The kernel signature and its docstring
were read in full; the kernel is the additive encoding of Nth roots of units.

`def-asd-finite-etale-tate-twist` defines `finiteEtaleTateTwist` and its explicit
roots-module/scalar-extension construction in
`Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist`, sourced to Section 03PK and the
finite scalar-extension/tensor-power operation used in the item's source.
It cites the general ordinary-étale roots node and the existing constant-ring
module equivalence. No matching finite ordinary-étale twist occurs in Mathlib,
the upstream project, or the DAG, as the recorded searches show. The three
sorry lemmas only certify annihilation and functor laws for explicit data;
annihilation determines the unique ZMod action, and no arbitrary data are
extracted from existence. The item directly cites this node, which cites the
roots node. The original item statement remains verbatim.

## Second reading by NK

I independently read the sandbox node and both delivered modules, the two new
nodes, the recorded statement dependencies and their declarations, and the Stacks
source text. Section 03PK defines the roots functor on arbitrary schemes and the
kernel of the power map; its Kummer lemma assumes the integer is a unit. Example
040M has no field, Noetherian, separatedness or nonemptiness assumption. Lemma
03RV concerns arbitrary schemes and finite locally constant sheaves. Scalar
extension and nonnegative tensor powers are the elementary operations specified
in the item's node, rather than additional hypotheses from those sources.

My object/hypothesis/conclusion inventory, with the Lean open:

| Node item | Lean rendering and verdict |
| --- | --- |
| Arbitrary scheme T | `(T : Scheme.{u})`: exact; no geometric assumptions. |
| Integer N at least one | `(N : ℕ) (hN : 0 < N)`: exact positive-integer range. |
| N invertible in every local ring | `∀ t : T, IsUnit (N : T.presheaf.stalk t)`: exact scheme stalks, not just residue fields. |
| Finite commutative coefficient ring A | `(A : Type (u + 1)) [CommRing A] [Finite A]`: exact, including the zero ring. |
| NA = 0 | `(hA : (N : A) = 0)`: exact, since annihilation of A implies this at 1 and this equality annihilates every element. |
| Ordinary small étale site | `T.Etale`, `T.smallEtaleTopology`: the recorded Mathlib site, not a pro-étale replacement. |
| Constant A and Z/N sheaves and their module sheaves | `constantSheaf`, `ModuleCat`, and scalar extension: exact under the recorded `etaleConstantModuleFunctor_isEquivalence`. I read its explicit realization, restriction, unit and counit. It preserves the underlying abelian presheaf and extends the constant scalar action. |
| μ_N as roots of units, with multiplicative group law | Upstream `rootsOfUnitySheaf` is `kernel (N • 𝟙 T.gmSheaf)`; `gmSheaf` is the universe-lifted additive encoding of units of `Γ(U, O_U)`. I read Kummer.lean and Gm.lean: exact roots and restriction maps. |
| Exponent action of Z/N on μ_N | `finiteEtaleMuModuleObj` uses `AddCommGroup.zmodModule`; `finiteEtaleMuModuleMap` uses `toZModLinearMap` on the same restrictions. I read both Mathlib declarations: exact action and maps. |
| A_T(1) = μ_N tensor A | `finiteEtaleTateLine` sheafifies `finiteEtaleMuModulePresheaf ⋙ ModuleCat.extendScalars (finiteEtaleTwistScalar N A hA)`. The scalar map is the concrete canonical ZMod cast. `extendScalars` forms A tensor μ_N, canonically the required object by tensor symmetry. Exact. |
| A_T(0) = A_T | Zero branch of `finiteEtaleTateTwist` is literally the constant regular A-module sheaf: exact. |
| Higher twists are tensor powers of the first | Degree one is the line, degree r+2 tensors degree r+1 with that line using `Sheaf.monoidalCategory`: exact positive powers. I read the sheaf monoidal construction and the dependency's ringed-site tensor and `positiveTensorPower` signatures. This constructs the twist, reusing tensor products; it does not duplicate a tensor definition. |
| For every r at least zero there exists a cover | `(r : ℕ)` precedes `∃ cover : Cover.{u} etalePrecoverage T`: exact order. The node does not demand a chosen simultaneous cover for all r. |
| Étale cover jointly surjects onto T | `Cover etalePrecoverage T`, converted by `cover.etalePrecoverageToEtale i`: exact recorded covering notion. |
| Restriction on every covering member is A as a module sheaf | `∀ i, Nonempty ((finiteEtaleTateTwist ... r).over (...) ≅ (constantSheaf ... (ModuleCat A)).obj (ModuleCat.of A A))`: exact; the isomorphisms retain the A-action and use the localized site. |
| Locally constant | `IsLocallyConstantSheaf (finiteEtaleTateTwist ... r)`: exact recorded definition. I read `LocallyConstantDatum` and its cover and `isConstant` fields. |
| Locally free of rank one | The same local isomorphisms to the regular module A assert precisely this, including the scalar action. No dimension or nonzero-ring hypothesis is inserted. |
| Flat: tensor preserves exact sequences | `PreservesFiniteLimits` and `PreservesFiniteColimits` of the displayed canonical `tensorLeft`: equivalent exactness for this additive functor between abelian sheaf categories. It preserves short exact sequences, hence arbitrary exact sequences by factoring through images, and conversely exactness supplies these finite limits and colimits. Exact strength. |

Edge cases: the empty scheme permits an empty covering and the unit hypothesis is
vacuous; a nonempty scheme cannot have an empty jointly surjective cover. The zero
coefficient ring is admitted and its regular module is still the free module on
one generator. N=1 forces that case and is admitted; N=0 is deliberately excluded
by the item's node but remains valid in the new definition (μ_0 is G_m and ZMod 0
acts by integer powers). r=0 is the constant sheaf, r=1 the actual scalar extension,
and r>1 the explicit recursion. Composite N and nonflat A over ZMod N are allowed:
the proof extends an isomorphism, not an arbitrary exact sequence over ZMod N.
Residue characteristic dividing N is excluded exactly by the unit hypothesis;
characteristic zero and mixed characteristic are retained. Universes are bound
explicitly and `autoImplicit false` is set. The coefficient universe u+1 is the
ordinary-étale convention used by the dependency; every finite ring can be
represented there, with no cardinal restriction. No extra finite-index-set or
nonempty-type assumption occurs.

Independent searches used different wording from the first reader. msearch
LeanFinder query "Small etale sheaf of units killed by n becomes a constant cyclic
module locally, and extension to torsion coefficients gives a flat line" returned
eight hits about étale ring algebras and `Module.isLocallyConstant_rankAtStalk`;
none defines or proves this statement. Loogle `"rootsOfUnitySheaf"` returned no
hits. LeanSearch "Nonnegative Tate twists of a finite torsion coefficient ring on
the ordinary etale site" was unavailable with Internal Server Error; I draw no
absence conclusion from that failure. These calls are recorded in searches.jsonl.
I also searched Mathlib AlgebraicGeometry, upstream WeilConjectures and project
lean/Sheaf with `tate.?twist|torsion.?twist|rootsOfUnitySheaf|cyclotomic.*sheaf`.
The Kummer roots sheaf is already reused. I opened Smooth/Conventions.lean:
`HasTateTwist.twistObject` is supplied derived twisting data, not this concrete
finite roots-of-unity module. WeilSheaf/TateTwist.lean defines l-adic Weil objects
over finite fields, also not this notion. Projective structure-sheaf twists are
different coefficients and sites. Exact-name searches in all three source trees
and dag/lean_names_upstream.json found no collisions for the delivered names.

For the new nodes I searched the whole DAG for roots-of-unity sheaves and inspected
`def-pur-roots-of-unity-sheaf`, `def-coefficient-twists-detailed` and
`def-sc-mu-trivialization`. These concern pro-étale completed coefficients or the
special-field trivialization; none supplies this general ordinary-étale notion.
`def-asd-etale-roots-of-unity` therefore correctly records the existing upstream
kernel, including N=0, without a new module. `def-asd-finite-etale-tate-twist`
correctly records the explicit construction and its constant-ring equivalence.
Both have self-contained statements, exactly the cited statement dependencies,
the item's chapter and unit, worker-created metadata, source places, searches,
empty proof fields, null mathlib_match, none audits, and the ancestor/via route.
Their statements agree with the source roots functor and the indicated scalar
extension/tensor-power construction. There are no dependency repair modules.

I also read the root-cover, primitive-root, constant-stalk and tensor-stalk
signatures used by the five-step proof. Their ring, scheme, module, and geometric
point parameters cover this application. The delivered main docstring carries
all five node proof steps and names their dependencies. All new declarations have
source/blueprint docstrings. Definitions contain explicit data; the three named
sorry lemmas only provide annihilation and functor laws, with complete proof
outlines, and the annihilation proof determines a unique ZMod action. All four
new theorem proofs are `sorry`; no mathematical proof was added at stage 2.

No mathematical or signature mismatch was found, so I left both Lean files and
all node statements unchanged. I added only this independent review. Both
modules compiled cleanly with scompile.py on the server (nice 19, two threads,
60 seconds per file; each delivered module took 1.9 seconds). The theorem and
new definition signatures match their node lean.statement fields verbatim.
