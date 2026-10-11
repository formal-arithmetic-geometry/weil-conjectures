## Worker report

The module `lean/Sheaf/AlgebraicGeometry/FinitelyPresentedComplexDescent.lean` states
`AlgebraicGeometry.exists_finitelyPresented_complex_of_limit`. Its sole theorem proof is
`sorry`; no definition, instance, auxiliary theorem, or proof is added. The original node
is unchanged except for `lean`; no new nodes or dependency modules are needed.

Hypotheses and clauses, matched individually:

- Directed set I: `{I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]`. A preorder permits
  the general directed-set convention in the standing brief. Fixing `(i : I)` supplies
  nonemptiness; no separate nonempty assumption is needed.
- The rings R_i and their compatible transition homomorphisms: `R : I ⥤ CommRingCat.{u}`.
  The inverse scheme system is `R.op ⋙ Scheme.Spec`, reversing these ring maps.
- Every R_i is Noetherian: `[∀ k : I, IsNoetherianRing (R.obj k)]`.
- S_i = Spec R_i: the objects of this scheme functor are precisely `Spec (R.obj k)`.
  Such schemes are automatically quasi-compact and quasi-separated; any morphism between
  affine schemes is affine. Thus none of those three clauses is omitted or imposed only
  on identity maps. They follow from the stipulated spectra, not hollow hypotheses.
- S = lim S_i = Spec R: `(c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]`.
  This retains an arbitrary limit representative with its projections, without requiring
  a chosen identification with a spectrum. `IsAffine c.pt` means it is isomorphic to one,
  exactly the coordinate-free rendering of S = Spec R. There is no assertion that the
  limit ring is Noetherian.
- Fix i and a finitely presented S_i-scheme X_i: `(i : I) {Xi : Scheme.{u}}
  (f : Xi ⟶ Spec (R.obj i)) [LocallyOfFinitePresentation f] [QuasiCompact f]
  [QuasiSeparated f]`. The three properties are exactly the convention node's definition
  of finite presentation. No separatedness, properness, flatness, or affineness of Xi is
  assumed.
- X = X_i ×_{S_i} S: `pullback f (c.π.app (op i))`.
- G is a Z-indexed family of O_X-modules with O_X-linear differentials to degree r+1,
  satisfying d^(r+1) d^r = 0: `G : CochainComplex (...).Modules ℤ`. Mathlib's `ComplexShape.up`
  specifies the degree-one differential; the morphisms of `X.Modules` are O_X-linear.
  `HomologicalComplex.d_comp_d'` supplies the zero-composite condition. Its additional
  off-shape differentials are required to be zero, so they introduce no extra data.
- Finitely presented terms: `hG_fp : ∀ n : ℤ, (G.X n).IsFinitePresentation`.
- Quasi-coherent terms: `hG_qc : ∀ n : ℤ, (G.X n).IsQuasicoherent`. This clause is explicit
  even though Mathlib's finite-presentation predicate already implies it.
- Zero outside a finite interval: `hG_bounded : ∃ a b : ℤ, ∀ n : ℤ,
  n < a ∨ b < n → IsZero (G.X n)`. `IsZero` says the module is a zero object, rather than
  prescribing a particular representative of it.
- Some j ≥ i: `∃ (j : I) (hij : i ≤ j) ...`.
- X_j = X_i ×_{S_i} S_j: `pullback f (Spec.map (R.map (homOfLE hij)))`.
- A bounded family H_j with the same kind of terms and differentials: `H : CochainComplex
  (...).Modules ℤ`, together with the three conjuncts giving finite-interval boundedness,
  finite presentation of every term, and quasi-coherence of every term. The complex
  structure includes the same O_Xj-linear degree-one differentials and d² = 0.
- Base change to X is isomorphic to G as a complex: the concluding family `e : ∀ n : ℤ,
  (Scheme.Modules.moduleBaseChange f ...).obj (H.X n) ≅ G.X n` and the equation
  `moduleBaseChange.map (H.d n m) ≫ (e m).hom = (e n).hom ≫ G.d n m` for all n,m.
  The base arrow is `Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)`, a morphism
  from S to S_j over S_i; its compatibility with S_i is the cone naturality equation.
  The recorded functor is tensor pullback along `baseChangeMap`, hence the genuine module
  base change. These are termwise isomorphisms, not only a quasi-isomorphism or derived
  identification; the commuting squares assemble them to an isomorphism of complexes.

Dependency declarations read and used:

- `def-pc-scheme`: Mathlib `AlgebraicGeometry.Scheme` and `Scheme.Hom`, in
  `Mathlib.AlgebraicGeometry.Scheme`; their full structure signatures and docstrings were
  read. The base scheme diagrams and module categories use these.
- `def-pc-morphism-conventions`: this is recorded as a convention node with no declaration
  or module. As its note instructs, use Mathlib `AlgebraicGeometry.LocallyOfFinitePresentation`,
  `QuasiCompact`, and `QuasiSeparated`, imported through
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`. Its definition includes all
  three properties, even though Mathlib does not bundle them into a finite-presentation
  class. The local finite-presentation signature and docstring were read.
- `def-pc-base-change`: `AlgebraicGeometry.Scheme.Modules.moduleBaseChange` in
  `Sheaf.AlgebraicGeometry.BaseChangeConventions` (imported), with its full signature and
  body read. It is `tensorPullback (baseChangeMap f g)`. The scheme pullbacks and induced
  map are its recorded Mathlib/source conventions; `baseChangeMap` and
  `isPullback_baseChangeMap` were read in `WeilConjectures.AlgebraicGeometry.PicardFunctor`.
- `pqf-def-coherent`: its module `Sheaf.AlgebraicGeometry.Coherent` records that the
  quasi-coherent clause is Mathlib `SheafOfModules.IsQuasicoherent`, in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` (imported). The module was read;
  its newly defined `RingedSpace.IsCoherent` is not used here, because the item asserts
  finite presentation and quasi-coherence, not Stacks coherence. The Mathlib
  `IsQuasicoherent` and `IsFinitePresentation` signatures and docstrings were read.
- `CochainComplex` and `HomologicalComplex` are existing Mathlib definitions in
  `Mathlib.Algebra.Homology.HomologicalComplex` (imported). Their signatures and defining
  fields were read. No new complex or boundedness notion is defined.

Source check: the local `literature/stacks-project/limits.tex` is absent on this machine.
I opened [Stacks Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR) and
[Tag 05LY](https://stacks.math.columbia.edu/tag/05LY). The first supplies descent of modules,
then maps between fixed models, then equality of maps. Its application to the finite
bounded family yields precisely the node's argument. The second concerns flatness and
is context only here: this item does not add a flatness hypothesis or conclusion.
The module docstring carries all four proof steps, with the proof-dependency node IDs.

Edge cases checked before writing:

- An empty index type cannot contain the given i. This is exactly the original scope;
  for a singleton index, the same stage j = i is allowed.
- A preorder need not be antisymmetric; `homOfLE` and the ring functor still encode all
  transition maps, and the cone equation still types.
- An empty X_i, empty limit scheme, or zero rings do not violate any binder. Zero modules
  and the zero complex fit `IsZero`; an empty support interval (a > b) is permitted.
- A complex concentrated in degree 0, arbitrary negative degrees, and arbitrarily long
  finite intervals fit the integer bounds. Nothing restricts the characteristic.
- An arbitrary nonaffine finitely presented Xi is allowed. No Noetherian condition on S
  or X is added. Index universe v and ring/scheme universe u are explicitly bound;
  there is no quantification over test algebras in an artificially smaller universe.

Searches (all performed before writing):

1. `msearch.py ... leanfinder` with query "A bounded complex of finitely presented
   quasi-coherent sheaves on a scheme descends along an affine inverse limit of schemes":
   eight hits, for structure-sheaf sections and maps of schemes in
   `Mathlib.AlgebraicGeometry.AffineTransitionLimit`; none concerns complexes of modules.
2. `msearch.py ... loogle` with query
   `HomologicalComplex, SheafOfModules.IsFinitePresentation`: zero hits.
3. `msearch.py ... grep` with query
   `complex.*descent|descent.*complex|exists.*complex.*limit` in `AlgebraicGeometry`:
   zero hits in Mathlib.
4. `msearch.py ... leansearch` with query
   "descent of bounded complexes of finitely presented quasi coherent modules along inverse
   limits": unavailable, Internal Server Error. No mathematical verdict drawn from it.
5. `rg -n 'complex.*descent|descent.*complex|lem-pc-fp-complex-descent'` in
   `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and repository `lean/Sheaf`:
   no source theorem; the landed `FlatBoundedComplexDescent.lean` cites this item in its
   proof but states a different result with flatness hypotheses and conclusions.
6. `rg -n 'exists_finitelyPresented_complex_of_limit'` in Mathlib, source, project Lean,
   and `dag/lean_names_upstream.json`: no collision. Reading Mathlib's existing complex
   and sheaf definitions avoided adding any private copies.

Server validation: `scompile.py G1 lem-pc-fp-complex-descent` compiled the 80-line module
in 4.7 seconds with exit code 0 and no warnings. No local Lean build was run.
No statement fault, correction, or disputed assertion was found.

## Second reading by G1

I read the node statement and the complete Lean signature independently. The objects and
hypotheses match as follows: the directed index `I` is rendered by `{I : Type u}` with
`[Preorder I] [IsDirected I (· ≤ ·)]`; the inverse affine system is
`R : I ⥤ CommRingCat.{u}` with `[∀ k : I, IsNoetherianRing (R.obj k)]` and
`R.op ⋙ Scheme.Spec`; its limit is `(c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c)`
with `[IsAffine c.pt]`. The fixed stage is `i : I`, and the finitely presented scheme over
`Spec (R.obj i)` is `Xi`, `f`, with the three Mathlib classes
`LocallyOfFinitePresentation`, `QuasiCompact`, and `QuasiSeparated`. The pullback
`pullback f (c.π.app (op i))` is the node's `X`, while the existential stage `j` and
`hij : i ≤ j` and `pullback f (Spec.map (R.map (homOfLE hij)))` are exactly `X_j`.

The complex hypothesis is `G : CochainComplex (...).Modules ℤ`; hence terms are
O_X-modules, differentials are O_X-linear, and the HomologicalComplex equations impose
`d^(r+1) ≫ d^r = 0`. The hypotheses `hG_bounded`, `hG_fp`, and `hG_qc` render finite
interval support, finite presentation, and quasi-coherence term by term. The conclusion
has a complex `H` over `X_j`, the same three properties, and termwise isomorphisms from
`Scheme.Modules.moduleBaseChange` of `H` to `G`; the final equality for every `n m : ℤ`
commutes each differential, so it is an isomorphism of complexes rather than merely a
quasi-isomorphism. No hypothesis or conclusion clause is missing or strengthened.

Edge cases are covered: an empty index type is excluded only because the statement fixes
`i`; singleton and non-antisymmetric preorders are allowed; zero rings, empty schemes,
zero modules, and a zero complex are allowed; the bounded interval may be empty; degree
zero and arbitrary negative degrees are allowed; no characteristic, separatedness,
properness, flatness, or affineness of `Xi` is added. I checked the dependency records and
used their recorded notions (`Scheme`, the finite-presentation morphism predicates,
`moduleBaseChange`, and `IsQuasicoherent`) rather than private copies. Searches recorded
in `searches.jsonl` and the worker report found no existing complex-descent declaration
in Mathlib, the source project, or `lean/Sheaf`.

The only mismatch found was the independent index universe `Type v` in the worker file;
the standing index-universe convention requires the limit index to live in the ring/scheme
universe. I changed the module to `universe u` and `{I : Type u}`. The node statement and
all other binders and clauses remain unchanged. No statement correction was needed and no
citer is affected.
