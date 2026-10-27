## Worker report

Item: lem-per-elkik-rational-smooth-models. The delivery states
`AlgebraicGeometry.exists_rational_smooth_pair_models` in
`Sheaf.AlgebraicGeometry.ElkikRationalSmoothModels`. Its entire proof is `sorry`;
there are no other postponed theorems or proof holes. Two new definition nodes provide
honest predicates and a structure of model data. No existing statement or dependency
record is corrected.

Source read: Temkin, Non-embedded Desingularization, arXiv:0904.1592v2,
https://math.huji.ac.il/~temkin/papers/Non_Embedded_Desingularization.pdf,
printed p.25, proof of Proposition 3.3.5. This is the rational approximation and
finite-stage shrinking argument, not the proposition's full resolution conclusion.
The printed factorization paragraph reverses X and Y; this delivery follows the
already-reviewed DAG's arrows h : Y_m -> X_m. The theorem docstring carries all eight
DAG proof steps, including the pair equations and the finite disjoint union argument.

Clause-by-clause correspondence:

- An affine pair (X,I): `IsPrincipalSingularityPair X I` requires `IsAffine X`.
  Its second conjunct is `∃ π : Γ(X, ⊤), π ∈ nonZeroDivisors Γ(X, ⊤) ∧
  I = Scheme.IdealSheafData.ofIdealTop (Ideal.span {π})`. On an affine scheme
  these are exactly ideals of its coordinate ring. No generator is chosen or forced
  to be preserved by a map.
- The singular-locus containment is the final conjunct
  `IsRegularScheme (Scheme.Opens.toScheme I.support.compl)`.
  All input components and all model stages are finite type over fields, hence
  locally Noetherian; regularity of this open is exactly absence of singular points
  outside V(I). The existing `IsRegularScheme` includes local Noetherianity.
- Finite type over a characteristic-zero field is
  `IsCharZeroVarietySingularityPair`: there exist `K : CommRingCat.{u}` and
  `s : X ⟶ Spec K`, with `IsField K`, `CharZero K`, `LocallyOfFiniteType s`
  and `QuasiCompact s`. The field and its structure morphism are existential.
  `IsField` does not assume an extra field structure or omit nontriviality.
- Finite disjoint unions are `IsFiniteCharZeroSingularityPair`: a natural number
  n, component schemes V and ideal sheaves J, an isomorphism `X ≅ ∐ V`, and
  `I.comap (Sigma.ι V i ≫ e.inv) = J i` on each component. Each component has
  its own existential characteristic-zero field. This includes n=1, so includes
  the original single-pair statement, and n=0, so includes the empty union.
- A small directed inverse system is `RationalSmoothPairSystem`: `Index : Type u`
  with `PartialOrder`, `Nonempty`, `IsDirected`, and `diagram : Indexᵒᵖ ⥤ Scheme.{u}`.
  The index has the same universe as the schemes, without a smaller independent
  universe that would miss the necessary coefficient rings. Universes are explicit.
- Its model ideals are `ideal a`; `pair a` is the principal singularity condition.
  `rationalMap` is a natural transformation to constant `Spec (.of (ULift.{u} ℚ))`.
  `finiteType` and `quasiCompact` say each model is finite type over Q. ULift
  places Q in the scheme universe, without restricting coefficient fields.
- All transition maps are affine and smooth in `transitionAffine` and
  `transitionSmooth`. `transitionIdeal` is equality of the extended target ideal
  with the source ideal, using existing ideal sheaf `comap`.
- The inverse limit as pairs is the cone `Cone.mk X projection` and its `isLimit`.
  `projectionIdeal` gives extension of each stage ideal to I;
  `projectionRegular` gives regularity of each projection. These data give the
  pair limit: the scheme universal map preserves ideals because its composite
  with any one stage projection does, and the index is nonempty.
- X_m and X_{a,m} are the actual closed subschemes `(I ^ m).subscheme` and
  `(ideal a ^ m).subscheme`. On an affine they are exactly Spec of the quotient
  coordinate rings. `thickIso` identifies the diagram objects with those canonical
  subschemes, `thickInclusion_eq` identifies their actual closed immersions, and
  `thickProjection_comm` specifies the commuting projection square.
  Naturality determines the transition maps, since the closed immersions are mono.
  Thus the fibre diagrams are canonical up to their specified isomorphisms, rather
  than arbitrary objects with an unrelated comparison map.
- For every `m : ℕ` with `1 ≤ m`, `thickIsLimit` gives the quotient limit and
  `thickProjectionRegular` gives regularity of every fibre projection. Ideal
  preservation on fibres follows from the commuting squares and the ambient
  ideal equalities by `comap_comp`; smoothness of fibre transitions follows by
  base change. The harmless m=0 diagram is the canonical empty closed subscheme;
  no regularity or limit assertion for m=0 is needed or used in the theorem.
- The existence conclusion is the first conjunct of the theorem: for every X,I
  satisfying the finite-union predicate there is `Nonempty (RationalSmoothPairSystem X I)`.
  This is an existence theorem; no data definition chooses a model via its sorry.
- The second conjunct quantifies independently over X,I and Y,J, their finite-union
  hypotheses, and arbitrary selected systems SX and SY. In particular it does not
  force a common coefficient field or a component-preserving map.
- The target index is `a : SX.Index`. The source lower bound is `b₀ : SY.Index`;
  the conclusion gives `b : SY.Index` with `b₀ ≤ b`. This explicitly allows
  increasing the source index while the target index remains fixed. Taking any
  lower bound recovers the existential formulation in the node.
- `h : (J ^ m).subscheme ⟶ (I ^ m).subscheme` is the given map of thick fibres.
  Its hypotheses are `IsRegularSchemeMorphism h` and
  `(I.comap (I ^ m).subschemeι).comap h = J.comap (J ^ m).subschemeι`.
  The second equality is exactly extension of I_m to J_m, not equality of chosen
  generators or a lift to Y -> X.
- The ambient source neighborhood is `U : (SY.diagram.obj (op b)).Opens`.
  The explicit `∀ y, ... y ∈ U` includes the image of all of Y_m in Y_b.
  `SY.fibreOpen m (op b) U` is the inverse image of U along the canonical closed
  fibre inclusion, exactly U_m = U ∩ Y_{b,m}.
- The maps p and v have precisely the types `Y_m ⟶ U_m` and `U_m ⟶ X_{a,m}`.
  `p ≫ U_m.ι = (SY.thickProjection m).app (op b)` ensures the first map is the
  induced source projection. `p ≫ v = h ≫ (SX.thickProjection m).app (op a)`
  is the requested factorization of the composite to the fixed target stage.
- `Smooth v` is the smoothness conclusion. The equality
  `(SX.thickIdeal m (op a)).comap v =
  (SY.thickIdeal m (op b)).comap U_m.ι` preserves the distinguished ideals.
  Here `thickIdeal` is exactly extension of the ambient ideal along the closed
  immersion. The last equality to Spec Q says v is a Q-morphism for the supplied
  compatible rational structure maps. There is no ambient map U -> X_a.

Statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; and the recorded quasi-compact clause
  `AlgebraicGeometry.QuasiCompact` from `Morphisms.QuasiCompact`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`:
  `AlgebraicGeometry.IsRegularScheme` (local Noetherianity and regular stalks).
- `Sheaf.AlgebraicGeometry.RegularSchemeMorphism`:
  `AlgebraicGeometry.IsRegularSchemeMorphism`, flat with geometrically regular
  fibres tested over every finite residue-field extension in the scheme universe.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
  The node's other clauses `SmoothOfRelativeDimension` and `Etale` were read;
  they are not needed to state this item.
- `Mathlib.CategoryTheory.Limits.HasLimits`: the limit/colimit universal property,
  `CategoryTheory.Limits.Cone`, `IsLimit`, dual to recorded `Cocone`, `IsColimit`.
  The directed preorder uses the standard category and opposite category instances.
- New dependencies `def-per-principal-singularity-pair` and
  `def-per-rational-smooth-pair-system`: the declarations listed in their records.
  Their further dependencies reuse `AlgebraicGeometry.Scheme`,
  `Scheme.IdealSheafData`, `Scheme.Hom.ker`, `IdealSheafData.ofIdealTop`,
  `IdealSheafData.comap`, `ideal_pow`, `subscheme`, `subschemeι`, and scheme
  coproducts. Ideal sheaves and powers are not redefined privately.

Every stated proof dependency's module is imported without `public`, except those
already publicly imported for the statement. Mathlib leaf files are imported too.
The currently unstated proof-only nodes `lem-per-char-zero-smooth-coefficient-system`
and `lem-per-regular-precomposition-smooth-image` have no module to import. They
are mentioned at the precise proof steps in the docstring; this delivery does not
need their statements for any type, so does not manufacture duplicate declarations.

Edge cases checked before and after writing: n=0 and empty schemes; n=1 and arbitrary
finite disjoint unions; I=O_X, with unit generator and empty thick fibres; nonreduced
pairs (not excluded); m=1 with possibly zero distinguished ideal on that fibre; m=0
excluded from the theorem; source and target with different fields; maps mixing finite
components; arbitrary prescribed source lower bound; arbitrary scheme universe u.
There is no injectivity/dominance/nonemptiness assumption on scheme projections or
on h. Nonzero-divisor membership uses its genuine zero-ring convention in the empty
case. The source-side open may be empty when Y_m is empty.

Searches performed, recorded by msearch.py in searches.jsonl:

1. leanfinder, "Principal singularity pairs in characteristic zero are limits of finite
   type rational schemes with smooth transitions and regular fibre projections":
   eight results, all standard smooth charts, relative dimensions, etale or smooth
   predicates; none defines this pair or the system or states the theorem.
2. loogle, "AlgebraicGeometry.Smooth, AlgebraicGeometry.IsRegularSchemeMorphism":
   zero hits; diagnostic unknown identifier for the project-only regular predicate.
3. grep, "Elkik|SingularityPair|rational.*smooth.*model", AlgebraicGeometry: zero hits.
4. leansearch, "Principal singularity pair affine scheme principal non zero divisor
   ideal regular complement rational inverse system": eight results about regular
   elements, principal ideals and localization; they supply individual ring notions,
   not the principal pair or its rational inverse system.
5. grep, "principal singularity|RationalSmoothPair|PrincipalSingularity|Elkik": zero hits.
6. loogle, "AlgebraicGeometry.Scheme.IdealSheafData, AlgebraicGeometry.Smooth": zero hits.

Direct rg searches in the allowed `lean/WeilConjectures` and `lean/Sheaf` trees found
ordinary rational linear models and the existing `SmallSingularLocusPair`, but that
notion has a generally non-affine excellent ambient scheme and a Cartier divisor
whose closed subscheme is a union of varieties; it is not this affine principal pair.
The exact item id has no upstream declaration. Searching the DAG finds the current
item and the smooth-span lifting theorem using the same informal input notion, but
no definition node. `blueprint_refs.py search 'principal singularity'` gave zero
nodes; searching 'rational smooth' gave only an unrelated dualizing-complex node.
`dag/lean_names_upstream.json` has no principal singularity/rational system match.
The individual Mathlib definitions found are all reused. No disputed statement found.

Validation: scompile.py was used for every compile, in dependency order, against the
live server library. All three delivered files compile cleanly, each in approximately
1.4--2.0 seconds. No lake build, direct git mutation or write in the shared repository
was performed. Final preflight and delivery results are recorded below when available.

## New nodes

`def-per-principal-singularity-pair` supplies the missing affine principal pair
predicate, the finite-type characteristic-zero specialization, and its finite disjoint
union form. Source: Temkin §3.2, §2.1.14 and proof of Proposition 3.3.5. The source
assertion already introduces this notion inline. Searches above find no existing DAG
notion or declaration; individual affine/ideal/non-zero-divisor/regular/finite-type
notions are reused. No new mathematical theorem is assumed in these definitions.

`def-per-rational-smooth-pair-system` supplies the model-system data used by the
existence and factorization clauses, plus its two canonical helper definitions
`thickIdeal` and `fibreOpen`. Source: proof of Temkin Proposition 3.3.5, p.25.
Searches above found inverse-limit and smoothness APIs, but no system bundling these
specified pair and thick-fibre conditions. It uses the preceding new node and the
existing smoothness, regular morphism, ideal powers and categorical limit APIs.
All fibre maps are tied by naturality and commuting squares to the specified closed
subschemes, rather than being arbitrary replacements for a canonical map.

## Second reading by Q65

A separate pass by this worker reopened the original node and all three Lean files.
No sub-agent was started, as the dispatch brief forbids it; the maintainer supplies
the independent review. This paragraph does not claim a separate independent reader.

The original node's single-pair input is covered through the n=1 case; the n=0
case remains available. Checked the full model fields against the first five node
clauses and the factorization signature against the remaining clauses: no coefficient
field compatibility is assumed, ideals are extended rather than their generators
preserved, and all positive fibre projections are regular. Checked that `thickIso`,
`thickInclusion_eq`, naturality and `thickProjection_comm` force exactly the actual
quotient maps. Checked p is the induced source projection and its composite with v
is h followed by the fixed target projection. Checked v is smooth, ideal-preserving
and rational, with its domain the open in the source thick fibre; no ambient lift is
present. Checked all quantifiers, including arbitrary systems and a fixed a while b
can increase. No mismatch was found in this pass. The only compilation repair was
qualifying the open-complement scheme as `Scheme.Opens.toScheme`; it changes no
mathematics. All declarations and universes are explicit and the final theorem is
sorry-only.

Final dry run: `deliver2.py Q65 lem-per-elkik-rational-smooth-models --no-push`
printed `OK (dry run): commit 7dbfeeea9d8 passes the preflight and compiles; nothing pushed`.
