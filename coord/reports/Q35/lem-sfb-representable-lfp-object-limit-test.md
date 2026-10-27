## Worker report

The module `Sheaf.AlgebraicGeometry.RepresentableLfpObjectLimitTest` states
`CategoryTheory.representable_lfp_iff_relative_objects_descend`, with `sorry` as its
only proof. The node's mathematical statement is unchanged. There are no new definitions.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| Arbitrary scheme S, with the size convention | `{S : Scheme.{u}}`; explicit `u v₁ w₁ v₂ w₂` |
| Two categories fibred in groupoids on S-schemes | `F` and `G : BasedCategory (Over S)` with independently sized total categories; `_hF : IsFibredInGroupoids F`, `_hG : IsFibredInGroupoids G` |
| Morphism commuting with cartesian pullback | `p : BasedFunctor F G`; every arrow of either CFG is strongly cartesian, so a functor over the base preserves cartesian arrows |
| Representable by algebraic spaces | `_hp : IsRepresentableByAlgebraicSpaces p`, using the existing equivalence of the actual 2-base-change groupoid with the discrete moduli category of an algebraic space, retaining its projection |
| Every representing map W_y to B is locally finitely presented on étale scheme charts | `ModuliSpaceTest @LocallyOfFinitePresentation p` |
| If and only if relative object descent | The outer `↔` |
| Every small nonempty directed system of affine S-schemes | `I : Type u`, `[Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]`, `D : Iᵒᵖ ⥤ Over S`, and `∀ i, IsAffine (D.obj (op i)).left` |
| With its limit T | `c : Cone D`, `Nonempty (IsLimit c)`; `c.pt` is T, with its projections `c.π.app (op i)` |
| Every i, y_i, and x | `i : I`, `yi : Functor.Fiber G.p (D.obj (op i))`, `x : Functor.Fiber F.p c.pt` |
| Isomorphism γ : p(x) ≅ y_i restricted to T | `γ : p.obj x.val ⟶ yi.val` with `G.p.IsHomLift (c.π.app (op i)) γ` |
| There exist j ≥ i and x_j | `∃ (j : I) (hij : i ≤ j) (xj : Functor.Fiber F.p (D.obj (op j)))` |
| Isomorphism α : x_j restricted to T ≅ x | `α : x.val ⟶ xj.val` with `F.p.IsHomLift (c.π.app (op j)) α` |
| Isomorphism β : p(x_j) ≅ y_i restricted to T_j | `β : p.obj xj.val ⟶ yi.val` with `G.p.IsHomLift (D.map (homOfLE hij).op) β` |
| β restricted to T = γ composed with p(α), under cartesian identifications | `p.map α ≫ β = γ` |
| No stack or finiteness assumption on F or G | No `IsModuliStack`, algebraicity, atlas, or finiteness hypotheses occur on F or G |

The total-category arrow encoding in the last four rows is exact. A CFG arrow over
f : V → B from a to b is the same as a fibre isomorphism a ≅ f* b. Consequently
Lean's α represents the inverse of the node's α. If the node's γ and β are denoted
γ₀ and β₀, Lean's equation becomes `β₀|T ∘ p(α₀⁻¹) = γ₀`, equivalent to
`β₀|T = γ₀ ∘ p(α₀)`. No chosen cleavage, arbitrary comparison, or isomorphism-class
quotient is substituted for the objects and compatibility data.

The existing `ModuliSpaceTest` quantifies over every scheme B and every based
functor h_B → G. By 2-Yoneda these are exactly objects y of G(B), up to the
cartesian identifications already allowed by the node. Its `HasSpaceBaseChange`
requires equivalence over the base, including the specified projection to h_B.
Requiring some such presentation with all étale scheme charts locally finitely
presented is equivalent to requiring this of every presentation, by invariance
under the unique representing-space isomorphism. Testing all étale charts instead
of just surjective atlases gives the same source-local finite-presentation property.
The target B is a scheme, so its identity chart suffices for the target chart test.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `def-weil-size-convention` is a metatheoretic convention without a declaration;
  schemes and directed indices use u; the two total categories retain separate
  object and morphism universes.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace` and
  `AlgebraicSpace.IsEtale`, inside the recorded representability/chart interfaces.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsFibredInGroupoids`, `IsRepresentableByAlgebraicSpaces`,
  `HasSpaceBaseChange`, `discreteModuli`, and `moduliTwoFiberProduct`.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`:
  `CategoryTheory.ModuliSpaceTest`. Its signature imposes no stack hypothesis.
- Mathlib's `BasedFunctor`, `Functor.Fiber`, `Functor.IsHomLift`, `Cone` and `IsLimit`
  provide the ordinary category-theoretic data.

The two already landed definition nodes carrying the additional interfaces are
added to `stmt_deps`, as authorized for landed nodes. They are not copied or repaired.
The two geometric proof prerequisites
`lem-sfb-space-relative-affine-limit-criterion` and
`lem-sfb-space-surjective-affine-limit-criterion` have no recorded Lean declarations
in the read repository; they remain named in the proof docstring and DAG, with no
speculative imports. The stated Mathlib proof leaf
`lem-weil-pbc-filtered-colimit-sets-elementwise` is imported via
`Mathlib.CategoryTheory.Limits.Types.Filtered`; its source signatures were read.

Edge cases checked before writing:

- A one-index system yields precisely descent over an isomorphism of bases.
- Empty affine schemes and the zero ring are allowed. No nonemptiness of a scheme,
  geometric point, coefficient ring, or fibre category is assumed.
- Empty F makes both the representing spaces and the relative descent problems empty;
  empty G makes the scheme-base-change tests vacuous. Both sides agree.
- Identity morphisms have trivial relative pair fibres and satisfy descent regardless
  of absolute limit preservation of the CFG.
- No affine, quasi-compact, or quasi-separated assumption on S is imposed, and there
  is no extra condition on transitions between the affine stages.
- The index set is nonempty as in the node. A preorder allows repeated/equivalent
  indices; no antisymmetry is imposed.
- The limit's affineness need not be an extra hypothesis: a nonempty directed limit
  of affine schemes is affine (`Scheme.isAffine_of_isLimit` in Mathlib). Limits of
  these nonempty connected diagrams in `Over S` agree with limits in schemes.

Source read: `literature/stacks-project/criteria.tex`, section-limit-preserving and
lemma-representable-by-spaces-limit-preserving (Tag 06CX), including both proofs.
The compatibility square in section-limit-preserving fixes the arrow orientation.
The withdrawn CompactObject example was also checked against its current recorded
upstream replacement `WeilConjectures.CategoryTheory.CompactObject`.

Searches for an existing theorem (2026-10-24):

- `msearch.py ... leanfinder` with “A representable morphism of categories fibered in
  groupoids is locally of finite presentation if and only if objects descend along
  directed affine inverse limits”: eight hits, scheme finite-presentation properties
  and ordinary categorical finite presentability; no matching theorem.
- `msearch.py ... leansearch` with “A representable morphism of fibered groupoids is
  limit preserving on objects if and only if locally of finite presentation”: eight
  hits, ordinary representable limit preservation and scheme local finite
  presentation; no relative CFG object-descent criterion.
- `msearch.py ... loogle` with
  `CategoryTheory.Functor.IsFiberedInGroupoids, CategoryTheory.Functor.Fiber`:
  no hits; the first name is not a Mathlib identifier.
- `msearch.py ... grep` for `IsFiberedInGroupoids|IsFibredInGroupoids|limitPreserving`
  in CategoryTheory, and for `IsFibredInGroupoids|IsRepresentableByAlgebraicSpaces`:
  no Mathlib match. Mathlib supplies the underlying fibre and based-functor machinery.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for CFG, representability,
  `ObjectsDescend`, `ModuliSpaceTest @LocallyOfFinitePresentation`, and representable
  limit/lfp combinations: found the existing general definitions used above, absolute
  object-descent definitions, and uses of the chart predicate, but no target theorem.
- Exact item-id search in `lean/WeilConjectures`: no result.

Validation: the delivered file compiled separately through `scompile.py` in both its
sandbox and library module locations (3.5 s and 3.3 s), with no errors or unexpected
warnings. All variables and universe levels are explicit and `autoImplicit` is false.
No statement dispute or source correction was needed.

## Second reading by Q35

A separate rereading in this worker session compared the node, source square, and
completed file. No second agent was started, as the dispatcher brief forbids it;
the maintainer's independent review remains the independent review of the delivery.
The rereading checked each row of the correspondence above. In particular, it
verified that α is encoded in the inverse direction, then composed to give exactly
the original compatibility equation; no comparison between underlying objects alone
was used. It checked that the chart predicate takes arbitrary CFGs rather than
assuming DM/algebraic stacks, and that representability retains the projection.
The explicit preorder, nonempty index, arbitrary base, and independent total-category
universes preserve the node's range. No mathematical mismatch or further change was
found. The only metadata adjustment adds the two already landed interface nodes to
`stmt_deps`; the statement and proof are unchanged.
