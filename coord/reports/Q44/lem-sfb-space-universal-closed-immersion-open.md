## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceUniversalClosedImmersionOpen` states
`AlgebraicGeometry.AlgebraicSpace.exists_openSubspace_universal_closedImmersion`.
Its only theorem proof is `sorry`; it introduces no definitions. The item node is
unchanged except for `lean`.

Source checked directly: `literature/stacks-project/spaces-more-morphisms.tex`,
Tag 05XA, `lemma-where-closed-immersion`, including its proof. The source gives exactly
local finite type and universal closedness of p, separatedness of q, and the universal
closed-immersion parameter condition. No statement correction or dispute is needed.

Clause-by-clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| S is a scheme | `{S : Scheme.{u}}` |
| A, C, B are algebraic spaces over S | `(A C B : AlgebraicSpace S)` |
| Universe convention | Explicit `universe u`; all spaces and test spaces use the recorded algebraic-space category over `Scheme.{u}` |
| p, q, f and q composed with f equals p | `(p : A ⟶ B) (q : C ⟶ B) (f : A ⟶ C)` and `(w : f ≫ q = p)` |
| p locally of finite type on compatible etale charts | `hp_lft : MapIsLocally (@LocallyOfFiniteType) p` |
| p universally closed on point spaces | `hp_closed : MapIsUniversallyClosed p` |
| q separated | `hq_sep : MapIsSeparated q` |
| There is an open subspace V of B | `∃ V : OpenSubspace B` |
| Every algebraic space T over S and every map h to B | `∀ (T : AlgebraicSpace S) (h : T ⟶ B)` |
| The canonical base change A ×_B T to C ×_B T | `pullback.map p.hom h.hom q.hom h.hom f.hom (𝟙 T.obj) (𝟙 B.obj) ...`; the two square equalities follow from w and the identity |
| Fibre products are sheaf fibre products | `p.hom`, `q.hom`, and `h.hom` are sheaf maps; `pullback.map` is formed in their sheaf category |
| f_T is a representable closed immersion | `IsRepresentableWith (fun _ _ r ↦ IsClosedImmersion r.left) (...).hom`, testing every scheme base change of that underlying presheaf map |
| If and only if h factors through V | `↔ ∃ l : T.obj.obj ⟶ V.val.toFunctor, l ≫ V.val.ι = h.hom.hom` |

The factor is a natural transformation into the recorded open subfunctor, exactly the
notion of factorization for this full subcategory of sheaves. The closed-immersion
predicate includes representability and the closed-immersion condition together;
there is no separate representability assumption on f or on h. Flatness, local finite
presentation, finite type, and properness are not added as hypotheses.

Recorded dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace` and
  `AlgebraicSpace.IsRepresentableWith`. The latter provides actual representing
  scheme pullback squares for every scheme test and the chosen scheme property.
- `def-weil-size-convention` is a convention record, implemented by the explicit
  universe binder, with no module to import.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`,
  `MapIsSeparated`, `MapIsUniversallyClosed`. Their definitions use respectively
  compatible etale scheme charts, the representable closed diagonal, and closed
  point maps after every algebraic-space base change.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace` is the subtype
  of subfunctors with representable open-immersion inclusion.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace` supplies the algebraic-space interpretation of the
  sheaf fibre products and their universal property. Its full signature/docstring
  and those of `etaleCover_pullback` and `etale_fibreProduct_isScheme` were read.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, applied
  through the recorded chart test rather than by changing its definition.

Proof dependencies already stated are imported publicly because they are also
statement dependencies. At inspection the other three proof dependencies
`lem-sfb-space-closed-subspace-proper`,
`lem-sfb-space-unramified-radicial-parameter-open`, and
`lem-sfb-space-closed-immersion-unramified-criterion` have neither Lean records nor
Mathlib matches. They are not needed to type this statement. Their future imports
are therefore omitted; their full proof uses remain in the theorem docstring.

Edge cases checked before writing:

- Empty A: the empty-to-C map stays a closed immersion under all base changes,
  so the represented condition is the whole base. No nonemptiness binder excludes it.
- Empty parameter T: both fibre products are empty, and the unique map to every
  open subfunctor factors h, so both sides hold.
- Empty B or empty C: the existing arrows enforce the appropriate empty sources;
  the formulation imposes no extra exclusions.
- Identity f: every base change is an isomorphism and hence a closed immersion;
  the locus is all B. More generally, a globally closed-immersion f gives all B.
- Nonreduced schemes/spaces and non-finitely-presented closed immersions are allowed;
  the predicate tests closed immersions, with no reducedness, Noetherian, flatness,
  finite-presentation, or extra separatedness assumption.
- The parameter quantification is over all algebraic spaces in the same recorded
  universe, not just schemes or field-valued points.

Searches performed with the prescribed wrapper:

- LeanFinder: `The base changes making a morphism of algebraic spaces a closed immersion form an open subspace when its source is locally finite type universally closed and its target separated`.
  Eight hits, including scheme `IsClosedImmersion.isStableUnderBaseChange`,
  `instHasOfPostcompPropertySchemeIsClosedImmersionIsSeparated`, and universal
  closedness stability/cancellation. None states the algebraic-space parameter locus.
- Loogle: `"IsClosedImmersion", "AlgebraicGeometry"`.
  Twelve hits, all scheme closed-immersion definitions and permanence results.
- Mathlib grep, subdirectory AlgebraicGeometry:
  `whereClosedImmersion|where_closed_immersion|closed.immersion.*locus|AlgebraicSpace`.
  Zero hits.
- LeanSearch: `The functor of base changes making a map of algebraic spaces a closed immersion is represented by an open subspace`.
  Eight hits, including scheme closed-immersion stability and open-immersion opens
  functors, with no exact match.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for universal closedness,
  closed-immersion/open locus names, `whereClosedImmersion`, and
  `where_closed_immersion`: no statement of Tag 05XA. The sibling
  `AlgebraicSpaceUniversalIsomorphismOpen` cites this item in its proof but states
  the different isomorphism condition. Read its `pullback.map` usage for consistency.
- The exact item-id grep in `lean/WeilConjectures` had no hits. Name/concept `rg`
  in `dag/lean_names_upstream.json`, `lean/WeilConjectures`, and `lean/Sheaf` found
  no existing declaration of this theorem. Existing representability and open-subspace
  notions are reused without a new definition or node.

Validation: the prescribed `scompile.py Q44 lem-sfb-space-universal-closed-immersion-open`
compiled the delivered module in both sandbox and library module modes on the server,
with no errors or warnings (1.6 s and 1.5 s). All universes and variables are explicit,
with `set_option autoImplicit false`.

## Second reading by Q44

Reread the node statement, the Stacks lemma, and the delivered signature clause by
clause after compilation. This is the worker's own second pass; the dispatcher brief
forbids starting another agent, and the maintainer provides independent review.
The base-change square is oriented correctly: w gives f followed by q equals p,
and `pullback.map` receives its symmetric sheaf equality as required. Taking `.hom`
then gives the presheaf map expected by `IsRepresentableWith`. The conclusion has
one common open V and all parameter maps h, with the closed-immersion condition on
the left and actual factorization on the right. Local finite type is not strengthened
to finite type, and separatedness is imposed only on q. No mismatch was found and
no correction was needed. The four docstring steps preserve the recorded proof plan.
