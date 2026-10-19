## Worker report

The module `Sheaf.AlgebraicGeometry.FixedFamilyEtaleSpanDescent` states
`AlgebraicGeometry.exists_fixedFamily_etale_span_descent`, with its sole proof `sorry`.
It also constructs `AlgebraicGeometry.fixedFamilyLimitProjection`, the canonical map
from a fixed model's pullback to the limit to its pullback at a later stage. Its data
are Mathlib's `pullback.map`, the identity on the fixed model, and the cone projection;
its compatibility proofs are existing category identities and `Cone.w`. It introduces
no independent mathematical notion and has no postponed data or helper theorem.

The node's statement and dependencies are unchanged. Its `lean` record lists both
public declarations, and its `statement` is copied verbatim from the theorem signature.
No new nodes or dependency repairs were necessary. No statement dispute was found.

Hypothesis-by-hypothesis correspondence:

| Node | Lean |
| --- | --- |
| Nonempty directed set I | `{I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]` |
| Inverse system of affine schemes | `D : Iᵒᵖ ⥤ Scheme.{u}` and `[∀ i : Iᵒᵖ, IsAffine (D.obj i)]` |
| B is its limit with projections p_i | `L : Cone D`, `hL : IsLimit L`; B is `L.pt`, p_i is `L.π.app (op i)` |
| Point b and all canonical κ(s_i) → κ(b) isomorphisms | `b : L.pt` and `hb : ∀ i : I, IsIso ((L.π.app (op i)).residueFieldMap b)`; s_i is the image of b |
| A fixed initial index | `i₀ : I` |
| Fixed affine models P₀,Q₀ over S_i₀ | `P₀ Q₀ : Scheme.{u}`, `[IsAffine P₀] [IsAffine Q₀]`, and their actual structure maps `fP`, `fQ` |
| Finite presentation of the two models | `[LocallyOfFinitePresentation fP] [LocallyOfFinitePresentation fQ]`; see the affine equivalence below |
| The fixed families P_j,Q_j | Literally `pullback fP (D.map (homOfLE hj).op)` and the corresponding expression for fQ |
| Their limit pullbacks P_B,Q_B | Literally `pullback fP (L.π.app (op i₀))` and the corresponding expression for fQ |
| Affine U of finite presentation over B | `U : Scheme.{u}`, `[IsAffine U]`, `fU : U ⟶ L.pt`, `[LocallyOfFinitePresentation fU]` |
| u lies over b | `u : U`, `hu : fU u = b` |
| a,c are morphisms into those fixed limit pullbacks | The binders `a` and `c` with precisely those pullback codomains |
| Both are B-morphisms | `ha : a ≫ pullback.snd ... = fU` and `hc : c ≫ pullback.snd ... = fU` |
| Both arrows are étale | `[Etale a] [Etale c]` |
| Both induced residue-field maps are isomorphisms at u | `haκ : IsIso (a.residueFieldMap u)` and `hcκ : IsIso (c.residueFieldMap u)` |

Finite presentation is represented here by local finite presentation on the affine
objects, without adding redundant quasi-compactness or quasi-separatedness hypotheses.
Every stage is affine, and `hL` implies that B is affine (Mathlib
`Scheme.isAffine_of_isLimit`). A morphism between affine schemes is affine and hence
quasi-compact and separated, so quasi-separated. Therefore each displayed local
finite-presentation assertion is equivalent to the node's full finite-presentation
assertion. This also applies to the existential stage source: `IsAffine Uj` occurs
alongside `LocallyOfFinitePresentation fUj`, and S_j is affine. No finite-presentation
condition has been weakened and no affineness hypothesis on B has been added.

Conclusion-by-conclusion correspondence:

| Node | Lean |
| --- | --- |
| Some j ≥ i₀ | `∃ (j : I) (hj : i₀ ≤ j)` |
| Affine source U_j over S_j of finite presentation | `∃ (Uj : Scheme.{u}) (fUj : Uj ⟶ D.obj (op j)), IsAffine Uj ∧ LocallyOfFinitePresentation fUj ∧ ...` |
| Stage arrows into the prescribed fixed models | The existential `aj`, `cj` have codomains the literal pullbacks of fP,fQ along the transition map at hj |
| Étale S_j-morphisms | `Etale aj ∧ Etale cj` and their two equations with `pullback.snd` equal to fUj |
| An isomorphism e : (U_j)_B ≅ U over B | `∃ e : pullback fUj (L.π.app (op j)) ≅ U`, with `e.hom ≫ fU = pullback.snd ...` |
| Both limit arrows are the actual base changes | `e.hom ≫ a ≫ fixedFamilyLimitProjection ... fP = pullback.fst ... ≫ aj`, and its fQ/c/cj counterpart, together with the equation over B |
| u_j is the projection of e⁻¹(u) | Used everywhere as the explicit term `(e.inv ≫ pullback.fst fUj (L.π.app (op j))) u`; no arbitrary stage point is substituted |
| x_j,y_j are the images of a(u),c(u) in the fixed stage models | Used as `fixedFamilyLimitProjection ... fP (a u)` and its fQ/c counterpart |
| a_j(u_j)=x_j and c_j(u_j)=y_j | The two explicit point equalities following the morphism equations |
| Canonical κ(x_j) → κ(a(u)) and κ(y_j) → κ(c(u)) are isomorphisms | The two `IsIso ((fixedFamilyLimitProjection ...).residueFieldMap ...)` clauses |
| Canonical κ(u_j) → κ(u) is an isomorphism | `IsIso ((e.inv ≫ pullback.fst ...).residueFieldMap u)`; this is exactly the projection after identifying the pullback source with U through e |
| Both stage arrows are elementary at u_j | The last two conjuncts `IsIso (aj.residueFieldMap (... u))` and `IsIso (cj.residueFieldMap (... u))` |

The base-change formulation uses projection equations rather than an uncharacterized
comparison map. Cartesian pasting identifies P_B with `P_j ×_{S_j} B`, preserving
both projections, and likewise for Q. Hence an arrow into P_B is uniquely determined
by its projection to P_j and its map to B. The displayed two equations and e's equation
over B say exactly that `e.hom ≫ a` is the actual base change of aj under this canonical
identification. The same argument applies to c. There are no existential target
replacements, arbitrary comparison maps, or choices of an abstract isomorphism between
target families. The canonical maps used by the residue-field conclusions are those
very fixed-family projections.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom` in
  `Mathlib.AlgebraicGeometry.Scheme`; affineness is Mathlib `IsAffine` in
  `Mathlib.AlgebraicGeometry.AffineScheme`, using its canonical Spec characterization.
- `pqf-def-affine-morphism`: `AlgebraicGeometry.IsAffineHom` in
  `Mathlib.AlgebraicGeometry.Morphisms.Affine`; used through the affine finite-presentation
  equivalence and by the recorded proof plan.
- `def-weil-pbc-category-colimit`: `Mathlib.CategoryTheory.Limits.HasLimits` and its
  limit/cone dual interface `Cone`, `IsLimit`, `Cone.w`. The node supplies categorical
  (co)limits, so a specified inverse limit is represented by a limiting cone rather
  than imposing equality with an arbitrarily chosen limit object.
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField` and
  `Scheme.Hom.residueFieldMap` in `Mathlib.AlgebraicGeometry.ResidueField`.
- `def-sbc-locally-finite-presentation`: `AlgebraicGeometry.LocallyOfFinitePresentation`
  in `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
- `def-weil-pbc-scheme-conventions` fixes no separate declaration; its finite-presentation
  convention is respected by the affine equivalence explained above.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`,
  `pullback.snd`, and `pullback.map` in
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale` in
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`; the old search-service name `IsEtale`
  is deprecated in the pinned source, so the statement uses `Etale`.

The stated proof dependencies are imported without `public`: `DescendAffine` and
`EtaleInverseLimitDescent` from `WeilConjectures.AlgebraicGeometry`,
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`, and
`Sheaf.AlgebraicGeometry.LimitAffineTransition`. The first two current upstream
sources were retrieved with `scompile.py --source` because they are absent from the
older local checkout. The Mathlib proof leaves are supplied by imports of
`Fiber`, `Pullbacks`, `Morphisms.QuasiSeparated`, and
`RingTheory.LocalRing.ResidueField.Ideal`, with the affine, étale and finite-presentation
modules already public for the signature. The theorem docstring gives all nine proof
steps, including the affine algebra presentation needed before descending étaleness.

Edge cases checked before writing: a singleton/constant directed system permits
j=i₀ and the evident source model; no strict inequality is required. Preorders need
not be antisymmetric. A pointed empty limit or pointed empty U supplies no b or u,
exactly as in the mathematical hypotheses. Empty target families likewise admit no
given arrows from a pointed U. No nonzero, finite, connected, Noetherian, smooth,
closed-point or characteristic assumption is imposed. The target structure maps
need not be étale. All scheme and index universes are explicitly bound, with I in
the scheme universe as required for inverse-limit statements. There are no statement
`let`, `have` or `show` expressions, local notation, or local instances.

Searches for an exact existing statement (all through the prescribed wrappers or
read-only source search):

- LeanFinder: `pointed etale span descent along an inverse limit of affine schemes
  keeping two target models fixed`. Eight hits, including the étale over-category,
  standard étale algebra lifting, and étale composition; no simultaneous pointed
  fixed-family descent theorem.
- Loogle: `"IsEtale", "IsLimit"`. Zero hits.
- Mathlib grep: `span.*descen|descen.*span|fixed.*[Ee]tale` in AlgebraicGeometry.
  Zero hits.
- LeanSearch: `An etale span to two prescribed finitely presented affine target
  families descends along an affine inverse limit with rational marked point`.
  Eight hits, including `Scheme.isAffine_of_isLimit`, affine limits, and individual
  morphism-property descent; no exact statement.
- `rg` with `span.*descen|descen.*span|lem-trf-fixed-family-etale-span-descent` in
  upstream WeilConjectures and project lean/Sheaf: unrelated matrix/graded-span,
  Hankel and sheaf-section results only. The literal blueprint-id `grep -rn` in
  upstream WeilConjectures returned no matches.
- `rg` of both new declaration names across Mathlib, upstream WeilConjectures and
  project lean/Sheaf returned no matches. The helper is just the explicit canonical
  pullback-map specialization required for this node, using the existing single
  definition of fibre products.

Source checked directly: `literature/stacks-project/limits.tex`,
`lemma-descend-finite-presentation` (01ZM), `lemma-descend-etale` (07RP), and
`literature/stacks-project/more-morphisms.tex`,
`lemma-relative-map-approximation-pre` (0GDX), especially the paragraph retaining
X_i and Y_i and the subsequent residue-field chain.

Validation: the complete module compiled cleanly through `scompile.py`; no errors or
unexpected warnings. The delivery dry run and push are performed after recording
this report. Every theorem proof is `sorry`; the canonical projection is real data.

## Second reading by N7

I reread the node and the Lean file side by side. The preorder, directedness and
nonemptiness hypotheses are the explicit `I` typeclass binders; the affine inverse
system, limiting cone, point, and all residue-field hypotheses are `D`, `L`, `hL`,
`b`, and `hb`. The fixed index, affine target models, structure maps, and local finite
presentation instances are `i₀`, `P₀`, `Q₀`, `fP`, `fQ`, and their instances. The
source `U`, its map `fU`, point `u`, point equation `hu`, span maps `a`,`c`, their
base equations, étale instances, and elementary residue-field hypotheses all occur
verbatim. The existential conclusion has exactly the node's later index and affine
finite-presentation source, the two prescribed pullback targets, étale stage arrows,
the `B`-isomorphism with its structure-map equation, both actual base-change
projection equations, the specified point images, all three canonical residue-field
isomorphisms, and the two elementary stage-arrow conclusions. No hypothesis or
conclusion was added, dropped, generalized, or replaced. The only repair was this
report section required by the returned-delivery shape check; the Lean module and
node statement were unchanged.
