## Worker report

The module `Sheaf.CategoryTheory.TensorActionTraceContraction` states
`CategoryTheory.tensorAction_trace_contraction`, with its entire proof postponed by `sorry`.
The helper `CategoryTheory.tensorTraceContraction` is the node's displayed construction of
`d`: its body is the actual composite `q ≫ (t ⊗ₘ 𝟙 B) ≫ (λ_ B).hom`.
It introduces no independent notion or postponed theorem. Both declarations are recorded
in `lean.declarations`. The node changes only in `lean`.

The source is the final canonical-reassociations sentence in the current blueprint's
`sec-smooth-purity/sk-thm-smooth-purity/lem-pur-projection-purity-agreement.proof.md`.
As the node explicitly records, this is an agent expansion of that sentence, not a formula
printed in the blueprint. I read that source and the node's complete five-step proof.
The theorem docstring preserves those five steps and their structural-coherence input.
There is no repair note for this item.

Every hypothesis and clause is rendered as follows:

| Node text | Lean rendering |
| --- | --- |
| Three monoidal categories | `X`, `Y`, `Z`, each with its own `Category` and `MonoidalCategory` instances. All three object universes and three morphism universes are independent, explicitly bound. |
| Functors `F_f`, `F_g` | `Ff : X ⥤ Y`, `Fg : Y ⥤ Z`. |
| Strong monoidal `P_f`, `P_g` | `Pf : Y ⥤ X`, `Pg : Z ⥤ Y`, and the recorded Mathlib notion `PfMonoidal : Pf.CoreMonoidal`, `_PgMonoidal : Pg.CoreMonoidal`. The latter remains a parameter although no tensorator of `Pg` appears in this calculation. |
| Inverse tensor comparison delta | `(PfMonoidal.μIso N N').inv`; its inverse in the action equation is `.hom`. |
| Associator and left unitor | Mathlib `(α_ M N N').hom`/`.inv`, `(λ_ B).hom`, in exactly the node's orientations. |
| Natural projection isomorphisms | `PFf` and `PFg` are families of `Iso` with source `F.obj M ⊗ N` and target `F.obj (M ⊗ P.obj N)`. `_hf_natural` and `_hg_natural` give their naturality for every pair of arrows between permitted pairs, in both variables. Naturality of the inverse follows from being an isomorphism. |
| They need only exist on full permitted domains | `Df : X → Y → Prop` and `Dg : Y → Z → Prop` specify arbitrary permitted pairs. A family component takes membership evidence, so there is no demand for a projection component outside its domain. Naturality quantifies over all arrows between permitted pairs: the domains are full. No monoidal structure on the domains is assumed. |
| Closure under every displayed projection component | `hfl`, `hft`, `hfs`, `hgl`, `hgc` supply precisely the three components of `PFf` and the two components of `PFg` that occur. Structural arrows exist in the ambient monoidal categories; functor images exist because the functors are ambient functors as in the node. |
| Tensor-action equation for `f` | `_hf_action`, with arbitrary `M`, `N`, `N'` and membership in each of the equation's three required components. Its factors, in Lean's first-to-last composition convention, are inverse associator, `PFf ⊗ 1`, the next `PFf`, and the image of associator followed by the forward tensorator. This is the node's equation read right to left. |
| Chosen objects and arbitrary traces | `Lf : X`, `Lg : Y`, `tf : Ff.obj Lf ⟶ 𝟙_ Y`, `tg : Fg.obj Lg ⟶ 𝟙_ Z`, with no normalization, adjointness or nonvanishing condition. |
| `q = PF⁻¹` | Each `.inv` of the supplied projection isomorphism. |
| Definition of `d` for every permitted coefficient | `tensorTraceContraction (PF... h).inv t`; the helper is defined for any coefficient object and any such inverse component. |
| `L = L_f ⊗ P_f L_g` | Written out as `Lf ⊗ Pf.obj Lg` wherever it appears. No local notation or statement-level `let` is used. |
| `a = d_f,Lg` | `tensorTraceContraction (PFf Lf Lg hfl).inv tf`. |
| `b = t_g F_g(a)` | `Fg.map (tensorTraceContraction (PFf Lf Lg hfl).inv tf) ≫ tg`. |
| Arbitrary permitted `K` | `K : Z` and the five membership hypotheses depending on `K`. |
| Canonical sigma reassociation | `(Lf ◁ (PfMonoidal.μIso Lg (Pg.obj K)).inv) ≫ (α_ Lf (Pf.obj Lg) (Pf.obj (Pg.obj K))).inv`. It first splits the pulled-back tensor product using delta, then reassociates. |
| Left side of the asserted equality | `Fg.map (tensorTraceContraction (PFf Lf (Lg ⊗ Pg.obj K) hft).inv tf) ≫ tensorTraceContraction (PFg Lg K hgl).inv tg`. |
| Right side of the asserted equality | In order: `Fg.map (Ff.map sigma)`, `Fg.map q_f,L,PgK`, `q_g,FfL,K`, `b ⊗ₘ 𝟙 K`, `(λ_ K).hom`. This is precisely the node's displayed order reversed to match `≫`. |
| Specified common source and target | Both sides elaborate from `Fg.obj (Ff.obj (Lf ⊗ Pf.obj (Lg ⊗ Pg.obj K)))` to `K`. |
| No adjunction or third-functor compositor | No such datum occurs in the signature. There is also no symmetry, braiding, unit normalization of the projections, or action equation for `g`. |

Dependency declarations were read in full, including their docstrings and fields:

- `def-sfb-monoidal-category` is the Mathlib leaf `CategoryTheory.MonoidalCategory`
  in `Mathlib.CategoryTheory.Monoidal.Category`, extending `MonoidalCategoryStruct`.
  Its associator, left unitor, tensor bifunctoriality and naturality are used directly.
- `def-sfb-strong-monoidal-functor` is the Mathlib leaf
  `CategoryTheory.Functor.CoreMonoidal` in `Mathlib.CategoryTheory.Monoidal.Functor`.
  I use that exact structure, including its actual specified tensorator isomorphisms.
- The sole further proof dependency, `lem-coef-monoidal-structural-coherence`, is
  `CategoryTheory.FreeMonoidalCategory.subsingleton_hom` in
  `Mathlib.CategoryTheory.Monoidal.Free.Coherence`. I read it and the interpretation functor
  `CategoryTheory.FreeMonoidalCategory.project` in `Free.Basic`. Its module is imported
  without `public` as a proof-plan dependency. The statement dependencies are exposed by
  the public import of `Mathlib.CategoryTheory.Monoidal.Functor`.

Edge-case checks by reading the types and the five proof steps:

- No additional nonempty-category hypothesis is added: each monoidal structure already
  supplies its unit object, and `Lf`, `Lg`, `K` are otherwise arbitrary chosen objects.
- All coefficient objects, including tensor units and zero objects when present, are admitted.
  Zero trace maps need no cancellation or nonvanishing assumption.
- For strict monoidal identity functors and identity projections the equation is exactly the
  successive contraction of `tf` and `tg`; associators and unitors specialize as expected.
- Rescaled projections are not silently normalized: the action equation for `f` is explicit,
  and no unit equation or action equation for `g` is required.
- Taking `Df` and `Dg` constantly true recovers projections defined on all pairs. Taking proper
  domains still requires only the five displayed components, and the naturality square used
  in proof step 4 has precisely the two `g` memberships supplied by `hgc` and `hgl`.
- Proof irrelevance makes a projection component independent of its membership proof;
  no choice of an extension of the isomorphisms outside the domain is used.
- No common-universe restriction is imposed; all six universes are explicitly declared.

Searches for an existing statement/notion (all through the prescribed `msearch.py` or
read-only source search):

- LeanFinder: `Successive contraction of two arbitrary maps to the tensor unit through
  natural inverse projection formula isomorphisms satisfying tensor action associativity`.
  Eight hits on associator conjugation, tensor interchange, and triangle laws; none is the
  two-functor trace contraction statement.
- Loogle: `"projectionFormula"`. Zero hits.
- Mathlib grep in `CategoryTheory`: `trace.*[Cc]ontract|projectionFormula|tensorAction`.
  Zero hits.
- LeanSearch: `In monoidal categories successive coefficient trace contractions factor
  through two natural projection isomorphisms with tensor action associativity`.
  Eight hits, including monoidal action associators and `associatorNatIso`; none states
  this identity for two supplied projection families and arbitrary coefficient functionals.
- Read-only `rg` with `trace.*[Cc]ontract|projectionFormula|tensorAction|` followed by the
  exact item id across both project Lean roots found unrelated additive tensor actions,
  projection-formula locality, and the upstream module-object projection formula.
  I read `Functor.ProjectionFormula` in
  `WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`: it concerns
  `P (S L ⊗ M) ≅ L ⊗ P M`, has a unit axiom, and requires full-domain coherence.
  It does not supply this node's right-sided, partially defined projection isomorphisms,
  and assuming it here would add a unit axiom absent from the node.
- Searches for `def .*([Cc]ontract|[Tt]race)|tensorTraceContraction` in Mathlib's monoidal
  directory and both project category-theory directories found only unrelated perfect traces,
  chain supertraces and absolute-trace exchanges. The exact new declaration names do not
  occur in `dag/lean_names_upstream.json` or either project Lean root.
- Exact-id project search found no existing declaration attached to this item. The current
  example module `Sheaf.CategoryTheory.CompactObject` is withdrawn; I also read its recorded
  replacement `WeilConjectures.CategoryTheory.CompactObject` for the current module style.

The first compile exposed a precedence error in the type of the dependent `Iso` families;
parenthesizing the isomorphism type fixed it. The final module compiles both as a sandbox
probe and at its real module name via `scompile.py`, with no errors or warnings. No theorem
is proved and no definition contains `sorry`. No statement correction or disputed statement
is needed.

## Second reading by Q112

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
