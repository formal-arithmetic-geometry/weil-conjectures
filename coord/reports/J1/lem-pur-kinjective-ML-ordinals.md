## Worker report

The module `Sheaf.Algebra.Homology.AcyclicLimitOrdinal` states
`CochainComplex.acyclic_limit_of_surjective_initialSegments`, with its sole proof `sorry`.
No definitions are introduced and no node statement or dependency list is changed.

Source checked: [Stacks Tag 0AAT, Lemma 12.31.8](https://stacks.math.columbia.edu/tag/0AAT).
The local `literature/stacks-project/homology.tex` is absent, so the official online text
was opened and read, including the entire transfinite induction proof. It agrees with
the node. The theorem docstring includes all five steps of the node's proof, including
the acyclicity justification for the arbitrary primitive at the limit step and the
final shift argument.

Clause-by-clause correspondence:

- An arbitrary ordinal is `(α : Ordinal.{u})`. Its preceding ordinals are represented
  by `α.ToType`, Mathlib's ordered small representative of precisely that ordinal
  (`Ordinal.ToType.mk : Set.Iio α ≃o α.ToType`). Thus this is not restricted to a
  countable ordinal or an ordinal with a last element.
- The cochain complexes of abelian groups, with integer degrees and square-zero
  differential, are `CochainComplex AddCommGrpCat.{max u v} ℤ`.
  Mathlib's `CochainComplex` is `HomologicalComplex` of shape `ComplexShape.up ℤ`;
  its structure includes the differential and square-zero laws.
- The compatible inverse system is the functor
  `K : α.ToTypeᵒᵖ ⥤ CochainComplex AddCommGrpCat.{max u v} ℤ`.
  `K.map (homOfLE h).op` is the transition from the larger to the smaller index;
  functor laws give identity and composition compatibility, and complex morphisms
  commute with the differentials.
- Every stage is acyclic: `hacyclic : ∀ β : α.ToType, (K.obj (op β)).Acyclic`.
  `HomologicalComplex.Acyclic` means `∀ n, ExactAt n`; `ExactAt` means exactness
  of the adjacent short complex. In abelian groups this is precisely kernel equals
  image in every integer degree, as required.
- For every stage and degree, the canonical map to the earlier inverse limit is
  surjective: `hsurj` quantifies `β`, `n`, and an arbitrary family
  `x : ∀ γ : Set.Iio β, (K.obj (op γ.val)).X n`. Its premise states exactly the
  compatibility equations for every `γ ≤ δ`, using the degree-`n` transition map.
  Its conclusion supplies `y : (K.obj (op β)).X n` whose image at every earlier
  `γ` is `x γ`. This is the elementwise surjectivity of the canonical map to the
  inverse limit, not merely surjectivity of individual transition maps. Identity
  arrows in the compatibility premise add only tautological equations.
- The conclusion `(limit K).Acyclic` is acyclicity of the inverse-limit complex.
  Mathlib's `HomologicalComplex.instHasLimit` constructs its terms as degreewise
  limits and its differential from the induced maps; evaluation preserves this
  limit. There is no additional limit-existence hypothesis.

Dependency declarations read and used:

- `def-sp-abelian` is a Mathlib leaf, recorded as `CategoryTheory.Abelian` in
  `Mathlib.CategoryTheory.Abelian.Basic`. Its complete class and docstring were
  read: preadditive with finite products, kernels, cokernels, normal monos and
  normal epis. `Mathlib.Algebra.Category.Grp.Abelian` imports this API and supplies
  its instance for `AddCommGrpCat`; the statement uses its abelian-group category.
  No duplicate or specialized replacement of the dependency is needed.
- Other existing Mathlib notions used directly: `Ordinal.ToType` and its order
  from `Mathlib.SetTheory.Ordinal.Basic`; `CategoryTheory.homOfLE` from
  `Mathlib.CategoryTheory.Category.Preorder`; `CochainComplex` and complex
  morphisms; `HomologicalComplex.Acyclic` / `ExactAt` from
  `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`; `limit` and the
  degreewise complex limit instance from
  `Mathlib.Algebra.Homology.HomologicalComplexLimits`. Their relevant definitions,
  signatures, and docstrings were inspected in the local source checkout.

Edge cases checked: `α = 0` allows the empty system and the zero terminal complex;
there is no nonemptiness binder. For the first stage, `Set.Iio β` is empty and
lifting its unique family simply requests an element of an abelian group, supplied
by zero. For successors the earlier compatible family is determined by its last
component; for limit stages all compatibility equations remain present. The zero
complex is allowed at any stage. Degrees range over all integers, including zero
and negative degrees, with no boundedness assumption. Universes `u v` are explicitly
bound; index size is `u` and group size is `max u v`, allowing small limits without
an extra hypothesis and covering arbitrary index/group sizes in a common universe.

Searches (2026-10-11):

- `msearch.py ... leanfinder "inverse limit of acyclic complexes indexed by ordinal
  with surjective maps to earlier limits"`: eight hits, including
  `HomologicalComplex.instHasLimit`, `isLimitOfEval`, `isLimitConeOfHasLimitEval`,
  AB5 results, and surjectivity for natural-number towers. None states this lemma.
- `msearch.py ... loogle "HomologicalComplex.Acyclic"`: twelve hits, including
  `Acyclic`, `acyclic_iff`, and opposite/truncation results. No ordinal limit theorem.
- `msearch.py ... grep "acyclic.*limit|limit.*acyclic" Algebra/Homology`: zero hits.
- `msearch.py ... leansearch "inverse limit acyclic complexes indexed by an ordinal"`:
  unavailable, Internal Server Error; no results could be obtained.
- `rg` on `WeilConjectures/` for `ML.over.ordinals|acyclic.*limit|limit.*acyclic`,
  and for `lem-pur-kinjective-ML-ordinals`: no matches. Search of `lean/Sheaf` found
  only K-flat closure prose and natural-number Roos-tower prose, not this statement.
- `rg` of `dag/lean_names_upstream.json` for `ML.over.ordinals|acyclic_limit_of|
  acyclic.*ordinal`: no matches. The chosen full theorem name was searched in
  Mathlib, `WeilConjectures`, `lean/Sheaf`, and the upstream name index: no collision.

Validation: server single-file compile succeeded in 1.4 seconds, with no errors or
warnings. No statement dispute, correction, missing notion, or unusable dependency
was found. The independent second reading is left to the assigned second reader.

## Second reading by J1

Read independently with the node, Lean module and source open. The source read was
Stacks `homology.tex`, section `section-inverse-systems` (lines 7587 onward) and
`lemma-ML-over-ordinals` (lines 7861–7917), fetched into the item's scratchpad from
https://raw.githubusercontent.com/stacks/stacks-project/master/homology.tex because
this machine has no local Stacks checkout. Also checked the official Tag 0AAT page.
The section introduces inverse systems in an arbitrary category; its discussion of
natural-number towers imposes no natural-number restriction on this ordinal lemma.
There are no ambient finiteness, boundedness, ring, or scheme hypotheses to add.

The node's objects, hypotheses and conclusion, matched individually:

1. An arbitrary ordinal alpha: `(α : Ordinal.{u})`. Verdict: exact. Read
   `Ordinal.ToType.mk : Set.Iio α ≃o α.ToType` in Mathlib's Ordinal/Basic.lean,
   so the indexing type is precisely all ordinals below alpha, with their order.
2. For each beta below alpha, an integer-graded complex of abelian groups:
   `K.obj (op β) : CochainComplex AddCommGrpCat.{max u v} ℤ`. Verdict: exact.
   `CochainComplex` uses the upward complex shape; its data include group objects,
   homomorphic differentials, and the square-zero laws. No boundedness is required.
3. Compatible transition chain maps from later to earlier stages:
   `K : α.ToTypeᵒᵖ ⥤ CochainComplex AddCommGrpCat.{max u v} ℤ`, with transitions
   `K.map (homOfLE h).op`. Verdict: exact. Read `homOfLE` in Preorder.lean;
   opposition reverses the map in the needed direction, functor laws impose
   identity/composition, and complex morphisms impose differential compatibility.
4. Every stage is acyclic in every degree: `hacyclic : ∀ β, (K.obj (op β)).Acyclic`.
   Verdict: exact. Read `HomologicalComplex.Acyclic` and `ExactAt`, and independently
   `ShortComplex.ab_exact_iff_range_eq_ker` in ShortComplex/Ab.lean: this is precisely
   image of the previous differential equals kernel of the next differential.
5. For each beta and each degree n the canonical map to the earlier inverse limit
   is surjective: `hsurj` quantifies `β`, `n : ℤ`, and every earlier family `x`.
   Its premise compares `x δ` and `x γ` by the transition for each `γ ≤ δ` in
   `Set.Iio β`; its conclusion gives one `y` with all earlier images equal to `x γ`.
   Verdict: exact. The compatible families are precisely the elements of the
   group inverse limit, so this is surjectivity of the canonical map. It includes
   all preceding indices at limit stages, rather than only adjacent transitions.
   Identity compatibility equations are tautological by the functor identity law.
6. The full inverse-limit complex is acyclic: `(limit K).Acyclic`. Verdict: exact.
   Read `coneOfHasLimitEval`, `isLimitConeOfHasLimitEval`, the `HasLimit` instance,
   and preservation by evaluation in HomologicalComplexLimits.lean. The complex
   limit is constructed degreewise, with the induced differential, exactly as in
   the source. The statement assumes no additional existence instance from callers.

Dependency audit: opened `def-sp-abelian` and its recorded Mathlib declaration
`CategoryTheory.Abelian` in Abelian/Basic.lean, including the actual class fields.
This node defines abelian categories (its label is not a definition of abelian
*groups*); the delivery correctly obtains the needed concrete groups from Mathlib's
`AddCommGrpCat` and the abelian-category instance in Algebra/Category/Grp/Abelian.lean.
Read that instance, whose target is `Abelian AddCommGrpCat.{u}`. This realizes the
structural dependency without treating an arbitrary abelian category as the source's
category of groups. No replacement dependency module or new definition is needed.
There are no new nodes, dependency modules, or statement corrections in this delivery.

Edge cases: alpha zero gives an empty diagram and its terminal zero complex;
no nonemptiness assumption excludes it. At the least beta the compatible family
is empty, and its lifting condition holds because zero is an element of every
abelian group. Alpha one imposes only stage acyclicity and this vacuous lifting.
For successors the earlier limit is represented by the largest preceding stage;
for limit ordinals the hypothesis still quantifies all earlier components.
Zero complexes and arbitrary unbounded complexes are included. Degree zero and
negative degrees are included by `ℤ`. No scheme, coefficient ring, or characteristic
occurs, hence no empty-scheme or characteristic case is restricted. Universes `u v`
are explicitly declared. The group universe `max u v` permits limits of a `u`-small
index and arbitrary group sizes in a common enlarged universe; there is no countable
ordinal restriction or smallness hypothesis on the group objects.

Independent searches (2026-10-11), using different search words from the worker:

- LeanFinder through `msearch.py`: `transfinite projective system exact chain
  complexes degreewise surjective initial segment projections`. Eight hits:
  Nobeling successor exactness, projective-resolution exactness, LightProfinite
  transition surjectivity, and degreewise exactness of short complexes. None states
  this ordinal inverse-limit lemma.
- Loogle through `msearch.py`: `"Acyclic", "limit"`. Zero hits. An earlier query
  without the comma was rejected by the query parser and supplied no evidence.
- LeanSearch through `msearch.py`: `Exactness of a projective limit of cochain
  complexes along a well ordered set`. Service unavailable (Internal Server Error);
  no mathematical verdict inferred from that failure.
- `rg` across all Mathlib, WeilConjectures, repository lean/Sheaf and the upstream
  name index: `acyclic.{0,80}(limit|ordinal)|(?:limit|ordinal).{0,80}acyclic|ML.over.ordinals`.
  Only unrelated right-derived acyclicity declarations and project docstrings
  concerning filtered colimits or natural-number Roos towers appeared. The direct
  search for transfinite/ordinal terminology in Mathlib/Algebra/Homology found no
  candidate. No duplicate definition or statement was found.

H5–H9: no definition is introduced, no proof is supplied beyond the one named
`sorry` theorem, no private notion is substituted, and all variables and universes
are bound. Module and declaration docstrings carry the source and blueprint id;
read the theorem's proof paragraph against all five node steps. It correctly uses
stage acyclicity for the initial primitive at a limit stage, the induction hypothesis
for the earlier-limit defect, degree-minus-two surjectivity for its lift, and shifts
for all degrees. Header, namespace, topic path and line widths follow conventions.
The node's `lean.statement` is the theorem signature verbatim.

Mismatches found: none. Changes: appended this independent second reading only;
the correct Lean module and node record were preserved. Recompiled the module with
`scompile.py J1 lem-pur-kinjective-ML-ordinals` on the server: exit code 0 in 1.4 s,
with no errors or warnings.
