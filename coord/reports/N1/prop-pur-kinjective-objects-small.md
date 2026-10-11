## Worker report

The module `lean/Sheaf/CategoryTheory/GrothendieckAbelian/ObjectsSmall.lean` states
`CategoryTheory.exists_factorization_of_subobject_cardinal_lt_cof`, with `sorry` as its
only proof. No new definitions, dependency modules or statement corrections are needed.

Source checked: Stacks Project, Injectives, Proposition 19.11.5, Tag 079F,
https://stacks.math.columbia.edu/tag/079F (the local Stacks checkout is absent).
Its statement and inverse-image/cofinality proof agree with the DAG node.

Hypotheses and clauses, individually:

- The category A is `{A : Type u} [Category.{v} A] [Abelian A]`.
- Grothendieck abelian is `[IsGrothendieckAbelian.{w} A]`, the recorded Mathlib notion
  of `def-sp-grothendieck-abelian`. This supplies small colimits, a generator and exact
  filtered colimits in the chosen small universe w. At w = v this is precisely the
  dependency's recorded ordinary Grothendieck convention; its general universe API also
  accommodates categories whose homs are merely w-small. No relation between object
  universe u and the small universe w is imposed.
- The object M is `(M : A)`.
- The ordinal is `(α : Ordinal.{w})`. Its entire predecessor order is represented by
  `α.ToType : Type w`, order-isomorphic to the ordinals strictly below α. This avoids
  making the index a type in w+1 and covers arbitrary small ordinal index sets.
- The size |M| is the cardinality of `Subobject M`. The hypothesis
  `(hsize : HasCardinalLT (Subobject M) α.cof)` means exactly that this cardinality is
  strictly below the cofinality: Mathlib's definition compares the two cardinals after
  lifting them to a common universe. Thus no separate definition of size or smallness
  is introduced. Well-poweredness follows from the Grothendieck instance.
- Every system is `(B : α.ToType ⥤ A)`: the preorder category has one arrow for each
  inequality, so functoriality is exactly coherence of transition maps.
- Monomorphic transitions are
  `(hmono : ∀ ⦃β γ : α.ToType⦄ (h : β ≤ γ), Mono (B.map (homOfLE h)))`.
  This includes every β ≤ γ, with no continuity requirement added at limit stages.
- The colimit is `(c : Cocone B) (hc : IsColimit c)`. An arbitrary colimit cocone
  expresses the same statement independently of a choice of canonical colimit;
  these colimits exist by the Grothendieck assumption.
- Every map into it is `(f : M ⟶ c.pt)`.
- Factorization through some stage is
  `∃ (β : α.ToType) (g : M ⟶ B.obj β), g ≫ c.ι.app β = f`.
  Here the component `c.ι.app β` is exactly the stage-to-colimit structure map.

Dependency declarations read and used:
`Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`,
`CategoryTheory.IsGrothendieckAbelian` (full class signature and docstring, lines 55–74),
with its colimit and well-poweredness instances. This is the sole statement dependency,
`def-sp-grothendieck-abelian`, whose status is mathlib and whose `mathlib_match` names
this class; it needs no `lean` record or replacement.
Other existing APIs: `CategoryTheory.Subobject`, `HasCardinalLT` from
`Mathlib.SetTheory.Cardinal.HasCardinalLT`, `Ordinal.cof` from
`Mathlib.SetTheory.Cardinal.Cofinality.Ordinal`, `Ordinal.ToType`, and `homOfLE` from
`Mathlib.CategoryTheory.Category.Preorder`.

Edge cases checked: for α = 0 the cofinality is zero, so the strict inequality is
impossible. For a successor ordinal the cofinality is one and every object has at least
one subobject, so again the hypothesis is impossible. The zero object has exactly one
subobject; it is included and the hypothesis entails a nonempty index. No nonzero
object, uncountability, regularity, continuous chain or chosen generator is required.
The ordinal index and Grothendieck colimit size use the same arbitrary universe w.
Universes u, v, w and all declaration binders are explicit.

Searches performed with `/home/ubuntu/weil-launcher/msearch.py N1
prop-pur-kinjective-objects-small`:

- leanfinder: "In a Grothendieck abelian category an object factors through a stage of
  a monomorphism ordinal colimit when cofinality exceeds the cardinality of its
  subobjects". Eight hits about generating monomorphisms and the small object argument;
  none states the ordinal/cofinality proposition.
- loogle: "Ordinal.cof, Subobject". No hits; unknown identifier Subobject.
- grep: "cof|Subobject|small" in CategoryTheory/Abelian/GrothendieckCategory.
  Found `ColimCoyoneda.lean`. Read its module docstring and the full
  `IsGrothendieckAbelian.IsPresentable.surjectivity` signature and proof: it uses
  a regular cardinal and a cardinal-filtered category, rather than this ordinal
  cofinality hypothesis. It is useful for proving the item but is not the same statement.
- leansearch: "Grothendieck abelian category objects small monomorphism ordinal
  cofinality subobjects". Unavailable: Internal Server Error.
- rg over Mathlib CategoryTheory, upstream WeilConjectures, local lean/Sheaf and
  dag/lean_names_upstream.json for the new declaration name, alpha.small, α.small,
  objects.*small, HasCardinalLT.*cof, and related cofinality/subobject patterns:
  no exact statement or name collision. Found the related local
  `BoundedSubobjectSize.lean` theorem, which uses cardinality of the same subobject
  lattice and states a different bounded-quotient result, not a size definition.
- grep -rn for "prop-pur-kinjective-objects-small" in upstream WeilConjectures:
  no hits. Read upstream `SerpeSmallObject.lean`, found by the broader small-object
  search: it applies the Mathlib cardinal-filtered preservation theorem to complexes,
  not this ordinal factorization statement.

Server compile: clean, exit 0, 1.2 seconds, no warnings. No STATEMENT-DISPUTED issue.

## Second reading by N1

Independently opened the repository node, sandbox node and Lean module, the sole
statement dependency `def-sp-grothendieck-abelian`, and its recorded Mathlib class.
Read the upstream Stacks `injectives.tex` (the local checkout is absent), in particular
`section-grothendieck-conditions`, `section-grothendieck-categories`, `definition-size`,
`definition-small`, and `proposition-objects-are-small` with its proof:
https://raw.githubusercontent.com/stacks/stacks-project/master/injectives.tex
and https://stacks.math.columbia.edu/tag/079F. The source has no fixed ring, field,
Noetherian condition, continuous-chain hypothesis or chosen generator in this proposition.
Its smallness definition asks for bijectivity of the Hom-colimit comparison; for mono
chains the injectivity is automatic, and the node explicitly spells out the remaining
factorization assertion. The Lean renders precisely that assertion.

Object/hypothesis/conclusion checklist, in source and quantifier order:

- A Grothendieck abelian category: `{A : Type u} [Category.{v} A] [Abelian A]
  [IsGrothendieckAbelian.{w} A]`. PASS. Read the class signature and docstring in
  `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`: local w-smallness,
  exact w-small filtered colimits and a separator; `hasColimits` supplies all w-small
  colimits. At w = v this is the dependency's recorded convention. The auxiliary w
  convention is also explicitly supported by Mathlib through `ShrinkHoms`, so no
  additional mathematical structure is imposed; the ordinary case is included.
- An arbitrary object M: `(M : A)`. PASS; no nonzero or finiteness restriction.
- Size is the number of subobjects: `Subobject M` is Mathlib's quotient of monomorphisms
  by subobject isomorphism, not the collection of representatives or merely objects
  admitting a mono. PASS; the Grothendieck `wellPowered` instance gives w-smallness.
  No second size definition is needed.
- An ordinal alpha with cofinality strictly greater than that size: `(α : Ordinal.{w})`
  and `(hsize : HasCardinalLT (Subobject M) α.cof)`. PASS. Opened `HasCardinalLT`:
  its definition is the strict comparison after cardinal lifts to a common universe,
  so using the potentially larger raw type `Subobject M` does not alter its size.
- Every coherent system on the predecessors of alpha: `(B : α.ToType ⥤ A)`.
  PASS. Opened `Ordinal.type_toType` and `Ordinal.ToType.mk`; the latter is an order
  isomorphism `Set.Iio α ≃o α.ToType`, so there is no lost predecessor or extra stage.
- Each transition beta <= gamma is monic: `hmono : ∀ ⦃β γ : α.ToType⦄
  (h : β ≤ γ), Mono (B.map (homOfLE h))`. PASS. The preorder category encodes exactly
  these inequalities and functoriality supplies coherence; all transitions, including
  identities, are covered. No requirement of continuity at limit stages is present.
- Its colimit and every map from M: `(c : Cocone B) (hc : IsColimit c)
  (f : M ⟶ c.pt)`. PASS. Quantifying over all colimit cocones is independent of a
  chosen representative of the colimit and adds no restriction on the systems.
- Factorization through some predecessor stage: `∃ (β : α.ToType)
  (g : M ⟶ B.obj β), g ≫ c.ι.app β = f`. PASS. The same f is factored through its
  stage-to-colimit component, in the correct composition order. No uniform stage,
  uniqueness clause or weaker image-only conclusion is substituted.

Edge cases: alpha = 0 has cofinality zero, so hsize is impossible; a successor has
cofinality one, while every M has at least its identity subobject, so hsize is again
impossible. These cases are covered, not excluded by an explicit Nonempty binder.
The zero object has exactly one subobject and is included for every admissible limit
ordinal. Constant chains and chains with zero stages are allowed. Empty schemes,
characteristic and n = 0 introduce no additional cases here because this proposition
is about arbitrary category objects, with no scheme, coefficient field or integer
parameter. Universes u, v, w are bound, unrestricted; both the ordinal index and the
small-colimit convention use w, avoiding an unrelated index universe.

Independent searches (2026-10-11), using different wording from the worker:

- LeanFinder through msearch: "A map from an abelian category object into a transfinite
  increasing union factors at a bounded stage if its subobject lattice has cardinality
  below the ordinal cofinality". Eight related hits about generating monomorphisms
  and the small object argument; none is this ordinal/cofinality statement.
- Loogle through msearch: `HasCardinalLT, Ordinal.cof`. Zero hits.
- LeanSearch through msearch: "Maps into increasing ordinal colimits of monomorphisms
  factor through a stage when the cofinality exceeds the number of subobjects".
  Service unavailable (Internal Server Error), recorded without a mathematical verdict.
- msearch grep `cofinal|factor|surject` was broad and returned unrelated hits; used
  focused rg instead over Mathlib, upstream WeilConjectures and repository lean/Sheaf:
  `factor.*cof|cof.*factor|HasCardinalLT.*Subobject|Subobject.*HasCardinalLT|objects.are.small|
  small.*monomorph|subobject.*cofinal`. Read the relevant full signatures in Mathlib
  GrothendieckCategory/Subobject and ColimCoyoneda, including
  `exists_isIso_of_functor_from_monoOver` and `IsPresentable.surjectivity`.
  They assume a regular cardinal and a cardinal-filtered index category, rather than
  directly stating this arbitrary ordinal/cofinality result. Also read upstream
  `SerpeSmallObject.lean`, which concerns complexes and a chosen regular cardinal.
  No exact duplicate. A separate rg for the full new declaration name over upstream
  and `dag/lean_names_upstream.json` found no collision.

H5-H9: no definitions or hidden data holes; the only theorem proof is `sorry`.
The declaration docstring carries all three proof steps (AB5 inverse images,
cardinality/cofinality bounded stage, pullback factorization) and the source/blueprint
marker. The module uses the conventional namespace, header, imports and line widths,
with no file-local notation, instances or private definitions. No new nodes,
dependency modules or statement_change exist, so H12/H13 and correction-citer checks
are inapplicable. The recorded lean.statement was checked verbatim against the signature.

Mismatches found: none. Changes: appended this independent reading only; preserved
both the correct Lean source and the node record. Validation: fresh single-file
scompile and deliver2 dry run are recorded by the delivery tools.
