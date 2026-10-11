## Worker report

Existing declaration; no module added. The statement is upstream
`AlgebraicGeometry.Etale.isIso_etaleLowerShriekToLowerStar`, in
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale`, line 682.
Its full signature and docstring, the comparison definition at line 654, and the
surrounding variable sections were read. Specialize the coefficient category A to
`ModuleCat.{u+1} Λ`, with `Λ : Type (u+1)` and `[CommRing Λ]`.
The concrete-category, filtered-colimit, Grothendieck-abelian and sheaf-composition
hypotheses are supplied by instances, rather than additional mathematical assumptions.
The scratch file `scratchpad/Check.lean` compiles cleanly with `inferInstance` for exactly
this specialization.

Hypothesis and clause correspondence:
- Schemes U and X: `{U X : Scheme.{u}}` in the specialization.
- Morphism π: `(π : U ⟶ X)`.
- Finite étale: `[IsFinite π] [AlgebraicGeometry.Etale π]`.
  The general upstream comparison also takes `[IsSeparated π]`, automatically supplied
  by finiteness; no separatedness assumption is added to the mathematical statement.
- Commutative coefficient ring: `(Λ : Type (u+1)) [CommRing Λ]`.
- Arbitrary sheaf of constant-coefficient modules M:
  `M : Sheaf U.smallEtaleTopology (ModuleCat.{u+1} Λ)`.
  This is the six-functor encoding explicitly authorized by the recorded
  def-weil-pbc-etale-sheaves; it does not require M to be finite or constructible.
- The canonical morphism c_M is
  `Etale.etaleLowerShriekToLowerStar (ModuleCat.{u+1} Λ) π M`, the SAME declaration
  recorded by def-weil-pbc-etale-shriek-to-star-map.
  Its source is `(Etale.etaleLowerShriek (ModuleCat.{u+1} Λ) π ‹_›).obj M` and its
  target is `(Etale.lowerStar (ModuleCat.{u+1} Λ) π).obj M`.
- Isomorphism as module sheaves: `IsIso` of this morphism in that sheaf category.
  Naturality in M is inherited from lowerStarUnit and the adjunction homEquiv used
  by the existing comparison definition: the map is the adjoint of the graph
  extension unit. No independently chosen isomorphism replaces the canonical map.

Dependency declarations used/read:
- Mathlib.CategoryTheory.MorphismProperty.Comma / OverAdjunction:
  `CategoryTheory.MorphismProperty.Over`, `Over.pullback`; the finite étale properties
  are Mathlib `AlgebraicGeometry.IsFinite` and `AlgebraicGeometry.Etale`.
- Mathlib.AlgebraicGeometry.Sites.Etale:
  `AlgebraicGeometry.Scheme.smallEtaleTopology` and `Scheme.Etale`.
- def-weil-pbc-scheme-conventions is a convention-only node, with no declaration.
- Sheaf.AlgebraicGeometry.EtaleSheaves: the recorded note authorizes the ModuleCat
  encoding of module sheaves; its set-valued predicates are not needed here.
- Mathlib.Algebra.Category.ModuleCat.Sheaf: `SheafOfModules` is the general ring-sheaf
  encoding; the authorized constant-coefficient encoding here is `Sheaf … (ModuleCat Λ)`.
- WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap:
  `AlgebraicGeometry.Etale.etaleLowerShriek` (sheafified sum-presheaf).
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs:
  `AlgebraicGeometry.Etale.lowerStar` (precomposition with étale base change).
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale:
  `AlgebraicGeometry.Etale.etaleLowerShriekToLowerStar` (adjoint of graph extension).

Edge cases: empty schemes and the empty finite étale fibre are allowed, with no
nonemptiness or positive degree assumption; zero M and the zero coefficient ring are
allowed; no characteristic, Noetherian, surjectivity, or finiteness of M is assumed.
There is no statement dispute or mathematical node fault. The node's numerical lemma
reference 59.70.6 is outdated; the stable source tag 03S7 currently displays 59.70.7,
with exactly this module-sheaf statement. Source checked at
https://stacks.math.columbia.edu/tag/03S7 (local literature text absent on this machine).

Searches:
- msearch leansearch: “finite etale extension by zero direct image isomorphism module
  sheaves”; service unavailable (Internal Server Error).
- msearch leanfinder: “finite etale extension by zero equals direct image for sheaves
  of modules”; eight unrelated formal-étale/ring/module-forgetful results, no match.
- msearch loogle: “IsIso, Sheaf, ModuleCat”; no hits, unknown identifier IsIso.
- msearch grep: “etaleLowerShriekToLowerStar|shriek.*star|extension.*direct image”;
  no Mathlib hits.
- rg in WeilConjectures and lean/Sheaf for comparison and shriek/star names:
  upstream FiniteEtale.lean contains the exact map and its isomorphism instance;
  no duplicate in lean/Sheaf. Inspected the surrounding source signatures/docstrings.
- grep of the item id in WeilConjectures: no hits (the exact instance has no node marker).
- rg of isIso_etaleLowerShriekToLowerStar in dag/lean_names_upstream.json: no hits;
  the current source and successful compiled #check confirm the declaration exists.

No new nodes, dependency modules, or statement correction are needed.

## Second reading by K1

I read the node statement, its source place (Stacks Project Lemma 03S7, formerly
numbered 59.70.6), the dependency records, and the upstream declaration. The
item-by-item correspondence is:

- The objects are schemes `U X : Scheme.{u}`, a morphism `π : U ⟶ X`, a commutative
  ring `Λ : Type (u+1)` with `[CommRing Λ]`, and an arbitrary module sheaf
  `M : Sheaf U.smallEtaleTopology (ModuleCat.{u+1} Λ)`. The Lean specialization of
  the upstream variables `{X Y : Scheme.{u}}`, `f : X ⟶ Y`, and
  `G : Sheaf X.smallEtaleTopology A` renders exactly these objects after
  `X := U`, `Y := X`, `f := π`, `A := ModuleCat.{u+1} Λ`, `G := M`.
- The finite étale hypothesis is `[IsFinite π] [AlgebraicGeometry.Etale π]`.
  The upstream instance additionally requires `[IsSeparated π]`, which is inferred
  from finiteness; this is not an extra mathematical assumption.
- The canonical map is exactly
  `Etale.etaleLowerShriekToLowerStar (ModuleCat.{u+1} Λ) π M`, with source
  `(Etale.etaleLowerShriek ... π).obj M` and target
  `(Etale.lowerStar ... π).obj M`, matching the cited comparison definition.
- The conclusion is `IsIso` of that map in the module-sheaf category. Naturality in
  `M` is part of the canonical transformation used to define the map, so no chosen
  noncanonical isomorphism is introduced. Every clause and quantifier agrees.

Edge cases were checked: empty `U` or `X`, empty finite fibres, the zero sheaf,
zero coefficient ring, degree zero, and arbitrary characteristic are all admitted;
no nonemptiness, surjectivity, Noetherian, or coefficient-sheaf finiteness is added.
The universe choice `Λ : Type (u+1)` and `M` in the corresponding sheaf category is
the coefficient encoding used by the six-functor declarations and does not exclude
any case of the node.

Searches were independently repeated with `rg` through Mathlib, `WeilConjectures`,
and `lean/Sheaf`, and with the recorded upstream-name index. No duplicate project
or Mathlib declaration exists. The upstream source contains the exact comparison
map and the instance `AlgebraicGeometry.Etale.isIso_etaleLowerShriekToLowerStar`
at `FiniteEtale.lean:682`; `scratchpad/Check.lean` typechecks the precise ModuleCat
specialization by `inferInstance`. No mismatch was found, so no Lean module or
statement correction is needed. The node copy was repaired only by adding its
`lean` record with this existing declaration.
