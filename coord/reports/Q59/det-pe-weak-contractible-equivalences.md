## Worker report

The module `lean/Sheaf/AlgebraicGeometry/ProEtale/WeakContractibleEquivalences.lean`
states `AlgebraicGeometry.Scheme.proetale_weakContractible_equivalences`.  For an arbitrary
scheme `X : Scheme.{u}` and object `W : X.ProEt`, it gives the two pairwise equivalences
between the three formulations in the node and the affine w-contractible consequence.
The representable sheaf is exactly
`(ProEt.topology X).uliftYoneda.{u + 1}.obj W`, with the site sheaf universe `Type (u + 1)`.
The proof is `sorry`, as required for a stage-2 statement.

The first equivalence renders clauses (1) and (2): for every sheaf `F` and epimorphism
`φ : F ⟶ h_W`, the existence of `s : h_W ⟶ F` with `s ≫ φ = 𝟙 _`; and `Projective h_W`. The existing Mathlib class `Projective` has exactly the
node's lifting field: for every epimorphism `φ : F ⟶ G` and map `y : h_W ⟶ G`,
there exists `s : h_W ⟶ F` with `s ≫ φ = y`. The second equivalence renders
clauses (2) and (3): `Projective h_W` is equivalent to
`Function.Surjective (φ.hom.app (op W))` for every epimorphism of sheaves `F ⟶ G`.
The final conjunct renders the affine assertion: for every `D : Type u` with
`[CommRing D] [IsWContractibleRing D]` and every weakly etale
`f : Spec (.of D) ⟶ X`, every epimorphism onto the representable of `ProEt.mk f` has a
section.

The statement uses these dependency declarations:

- `CategoryTheory.Projective` from `Mathlib.CategoryTheory.Preadditive.Projective.Basic`,
  the existing projectivity class (no second definition of the lifting property).
- `AlgebraicGeometry.Scheme.proetale_site_properties` from
  `Sheaf.AlgebraicGeometry.Sites.ProetaleSiteProperties`, which supplies the small
  pro-etale topology, subcanonical representables, and the sheaf topos framework.
- `CategoryTheory.Precoverage.IsSiteForCoverings` from
  `Sheaf.CategoryTheory.SiteCoveringAxioms` (through the site-properties module), the
  site/sheaf interface for `ProEt.topology`.
- `IsWContractibleRing` (with its inherited `WLocalSpace`, `IsWLocalRing`, and
  `IsWStrictlyLocalRing`) from `WeilConjectures.RingTheory.ProEtale.WContractible`.
- `AlgebraicGeometry.Scheme.proetale_wContractible_projective` from
  `Sheaf.AlgebraicGeometry.ProEtale.Projective`, used for the final affine section
  assertion.

Edge cases checked: if `W` is empty, the empty cover forces singleton sections of
every sheaf, so evaluation is surjective and the representable is projective. A
disconnected `W` is not required to lift into just one member of a covering family;
the section is of the entire epimorphism. The zero-ring affine case is included
(no `Nontrivial D` assumption). There is no characteristic, finiteness,
connectedness, nonemptiness, or separatedness assumption.  The site object and
morphism universes remain distinct in the standard convention: `X`, `D`, and `f` use
universe `u`, while sheaf values and the representable use `Type (u + 1)`; no universe
was collapsed.

Searches made on 2026-10-17:

- `msearch.py ... leanfinder "equivalent forms weakly contractible representable sheaf projective epi sections surjective"` returned only general `CategoryTheory.Projective` and coyoneda-preservation declarations; no complete match.
- `msearch.py ... loogle "CategoryTheory.Projective"` returned the exact projectivity class and general projective-object API, but no complete match. The preceding combined query with `CategoryTheory.GrothendieckTopology.IsWeaklyContractible` was rejected by Loogle because that upstream name is not in the Mathlib index; that rejected query gives no evidence of absence.
- `msearch.py ... grep "IsWeaklyContractible|weaklyContractible|Projective" CategoryTheory` found only general Mathlib projectivity declarations, with no pro-etale weak-contractibility equivalence.
- `rg -n "WeaklyContractible|weaklyContractible|weak contractible"` over the project and source found the existing generic `IsWeaklyContractible` framework and the affine projectivity theorem, but no declaration of this complete equivalence statement.

The existing generic terminology `CategoryTheory.GrothendieckTopology.IsWeaklyContractible`
was read with `scompile.py --source WeilConjectures.CategoryTheory.Sites.WeaklyContractible`.
It uses locally surjective sheaf morphisms; the recorded Mathlib
`CategoryTheory.Sheaf.isLocallySurjective_iff_epi` identifies that with condition (3).
The theorem records the terminology in its docstring and introduces no new definition.
The proof imports include both recorded Mathlib leaves `CategoryTheory.yonedaEquiv`
(`Mathlib.CategoryTheory.Yoneda`) and the local-surjectivity criterion
(`Mathlib.CategoryTheory.Sites.LocallySurjective`); their source signatures and docstrings
were read. The docstring follows all five DAG proof steps, including the explicit
pullback sheaf and verification that its projection is epi.

No `STATEMENT-DISPUTED` issue or node fault was found.  The required `scompile.py`
compile of the final file completed cleanly in 1.8 seconds with no diagnostics.
Only the item's `lean` field changes in the node copy; no new node, dependency repair,
or statement correction is needed.

## Second reading by Q59

I read the node statement, its blueprint source, the Stacks weak-contractibility
definition and pro-etale affine lemma, and the Lean module independently. The objects
and clauses match as follows. The node introduces an arbitrary object `W` of
`X_{proét}` and its representable sheaf `h_W = Hom_X(-, W)`; Lean renders these as
`(X : Scheme.{u})`, `(W : X.ProEt)`, and
`(ProEt.topology X).uliftYoneda.{u + 1}.obj W`. The sheaf category is
`Sheaf (ProEt.topology X) (Type (u + 1))`, supplied by the recorded pro-etale site
properties, so the site and value universes agree with the project's size convention.

The first conclusion clause is exactly condition 1: for every sheaf `F` and every
epimorphism `φ : F ⟶ h_W`, Lean has `[Epi φ]` and produces
`s : h_W ⟶ F` with `s ≫ φ = 𝟙 _`. The first equivalence identifies this with
`Projective h_W`, whose Mathlib lifting field is precisely the node's condition 2:
every epimorphism and every map out of `h_W` admit a lift. The second equivalence
renders condition 3 with the same quantifier order: arbitrary sheaves `F`, `G`, and
an epimorphism `φ : F ⟶ G`, followed by
`Function.Surjective (φ.hom.app (op W))`, which is the map `F(W) → G(W)`.
The final conjunct quantifies arbitrary `D : Type u` with `[CommRing D]` and
`[IsWContractibleRing D]`, an arbitrary `f : Spec (.of D) ⟶ X` with
`[WeaklyEtale f]`, and every epimorphism onto the representable of `ProEt.mk f`,
then gives exactly a section. No hypothesis is added or omitted.

The source's weakly contractible definition uses surjections of sheaves and the
pro-etale source lemma identifies w-contractible affines with this property. The
node itself phrases these maps as epimorphisms; Lean follows that wording with
`Epi`, while retaining the sheaf-evaluation map for condition 3. The affine clause
uses the recorded `proetale_wContractible_projective` dependency and does not add
nontriviality, characteristic, finiteness, connectedness, separatedness, or
nonemptiness assumptions.

Edge cases checked: `W` may be empty or disconnected; `D` may be the zero ring;
there is no characteristic restriction; and the arbitrary universe `u` is retained
with sheaf values in `Type (u + 1)` and evaluation at `op W`. The quantifiers permit
empty sheaves, empty covers, and all affine and non-affine objects covered by the
node.

For one-definition-per-notion checks, I searched the blueprint DAG, Mathlib, the
project's `lean/Sheaf`, and the slopmaster2 `WeilConjectures` sources. Independent
LeanFinder/LeanSearch/Loogle queries for weak-contractible representables,
projective epi splitting, and evaluation-surjectivity found only the general
`CategoryTheory.Projective`, Yoneda, and locally-surjective APIs. Grep for
`WeaklyContractible`, `weakly contractible`, and `projective` likewise found no
complete declaration. The existing `CategoryTheory.Projective` class and the
recorded pro-etale site/projectivity declarations were opened and used directly.

No mismatch was found, so no file, node field, dependency interface, or statement was
changed in this second reading. The module compiles cleanly with `scompile.py` and
contains only the required postponed theorem proof.
