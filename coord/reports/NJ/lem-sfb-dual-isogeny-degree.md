## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianVariety.DualIsogenyDegree` states
`AlgebraicGeometry.IsIsogeny.dual_isogenyDegree_eq`, with its sole proof `sorry`.
It also constructs `AlgebraicGeometry.abelianSourceRigidificationPullback`, the canonical
identity-axis trivialization of a family pulled back in its first coordinate. This helper
belongs to the classifying-family clause of this node; it is not an independent notion,
uses no existence choice, and has no postponed proof. Both declarations have source and
blueprint docstrings. The theorem docstring gives all seven steps of the DAG proof.

Source read: `literature/milne-abelian-varieties_AV.pdf`, printed pp.36–37 and 41
(PDF pages 42–43 and 47), especially the opening paragraph of §9 and Theorem 9.1.
The source states the stronger kernel identification with the Cartier dual; the node asks
only for its isogeny and scheme-theoretic degree consequences, which are exactly the two
conclusions here. No statement correction or dispute was needed. The source explicitly
covers the general-field case by its Oort reference.

Hypothesis and clause correspondence:

- Any field k: `{k : Type u} [Field k]`, with an explicitly declared universe.
- A and B over k: `{A B : Over (Spec (.of k))}`; their group schemes are
  `[GrpObj A] [GrpObj B]`, and properness, smoothness and connectedness are precisely
  `[IsAbelianVariety A] [IsAbelianVariety B]`.
- Normalized dual Poincare data: `(DA : AbelianDualPoincareDatum A)` and
  `(DB : AbelianDualPoincareDatum B)`. The recorded structure supplies the dual abelian
  varieties, invertible universal modules, both axes, geometric fibre condition, universal
  property for every parameter scheme and rigidification, and tensor group law.
- Isogeny u: `(u : A ⟶ B) [IsIsogeny u]`; the recorded class extends `IsMonHom u` and
  `Surjective u.left` and contains finiteness of `(GrpObj.ker u).hom`.
- Homomorphism u-dual in the required reverse direction:
  `(uDual : DB.dual ⟶ DA.dual) [IsMonHom uDual]`.
- Its classifying family: `hDual` quantifies an isomorphism `i` from the pullback of
  `DA.poincare` by `(A ◁ uDual).left` to the pullback of `DB.poincare` by
  `(u ▷ DB.dual).left`. These are precisely 1 × u-dual and u × 1.
- Respect for the identity-axis rigidification: the equation in `hDual` says that pulling
  `i.hom` back by `abelianIdentityAxis A DB.dual` and composing with the source-pulled
  rigidification equals `abelianRigidificationPullback ... uDual`, the already recorded
  parameter-pulled rigidification. Thus it is the specified rigidified classification,
  rather than just an isomorphism of unrigidified modules.
- Dual is an isogeny: first conjunct `IsIsogeny uDual`.
- Degree equality: second conjunct `isogenyDegree uDual = isogenyDegree u`.
  The recorded degree unfolds to `(GrpObj.ker f).hom.finrankΓ`; `finrankΓ` is the
  dimension of the actual global-section algebra with its structural k-action. Neither
  kernel points nor a reduced kernel occurs.
- No perfection, separability, or characteristic restriction: there are no such binders.

Dependency interfaces read and used:

- `def-weil-field`: Mathlib `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-sc-abelian-variety`: `AlgebraicGeometry.IsAbelianVariety`,
  `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`.
- `def-sfb-abelian-dual-poincare-datum`: `AbelianDualPoincareDatum`,
  `abelianIdentityAxis`, `abelianRigidificationPullback` in
  `Sheaf.AlgebraicGeometry.AbelianVariety.DualPoincareDatum`. Read the full module locally
  and confirmed the identical live source with `scompile.py --source`.
- `def-sc-isogeny`: `IsIsogeny`, `isogenyDegree`,
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`, including their full definitions.
- `def-sc-group-scheme`: Mathlib `CategoryTheory.GrpObj`, `IsMonHom`, and the existing
  `GrpObj.ker` implementation supplied through the upstream group-scheme module.
- `def-pc-module-pullback`: public import of its recorded
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`. The signature follows the
  Poincare datum's existing `Scheme.Modules.pullback`, `pullbackComp`, `pullbackCongr`
  interface (Mathlib.AlgebraicGeometry.Modules.Sheaf), as does its rigidification.
  This is the sheaf-module inverse image, canonically left adjoint to the same pushforward;
  the tensor construction in the recorded dependency gives the equivalent tensor formula.
  No new inverse-image functor or arbitrary comparison is introduced. The source-axis helper
  uses the same canonical comparisons as the existing parameter-axis helper.

All presently recorded proof-dependency modules are imported privately, including descent,
global sections, flat base change, abelian variety structure and isogenies, and the kernel.
`Mathlib.FieldTheory.IsAlgClosed.Basic` supplies the finite-extension algebraic-closure input;
the algebraic-equivalence module is already publicly imported by the Poincare datum.
The five new stage-1 prerequisites (homogeneous-line algebraic triviality, isogeny
quasi-inverse, algebraically-trivial-line multiplicativity, finite Cartier representability,
pointed torsor character descent) currently have no recorded Lean modules, so they cannot yet
be imported. They are proof dependencies only, not missing objects needed in this signature.
They remain in the unchanged DAG and are explicitly cited in the proof docstring.

Edge cases checked before writing: zero-dimensional abelian varieties and the identity
isogeny (degree one); nonreduced kernels of characteristic-p multiplication and inseparable
isogenies (the degree retains their length); imperfect base fields (no extra assumption);
arbitrary supplied dual data (no chosen model or polarization); and nonreduced parameter
schemes in rigidified classification (the supplied datum retains these). The empty scheme
cannot be an abelian variety because it cannot carry a unit section over a field. A zero map
is considered only when it actually satisfies `IsIsogeny`; no independent exclusion is added.

Searches before writing (all on the named read-only trees or via the prescribed wrapper):

- msearch LeanFinder: "The dual of an isogeny of abelian varieties is an isogeny of the
  same degree". Eight hits on linear/base-change/character-module duality; no match.
- msearch Loogle: `IsIsogeny, isogenyDegree`. Zero hits, unknown identifier `IsIsogeny`
  in Mathlib; the upstream definition was found directly and used.
- msearch grep in Mathlib AlgebraicGeometry: `dual.*isogen|isogen.*dual|Poincare`.
  Zero hits.
- msearch LeanSearch: "The dual of an isogeny of abelian varieties preserves the order
  of its finite scheme theoretic kernel". Eight unrelated order-dual hits; no match.
- rg of Mathlib, `lean/WeilConjectures`, and `lean/Sheaf`:
  `dual.*isogen|isogen.*dual|DualIsogeny|dual_isogeny`. Only a nearby ample-polarization
  docstring, not the theorem. Exact blueprint-id search of `lean/WeilConjectures`: no hit.
- Exact declaration-name search in Mathlib, the source repository, `lean/Sheaf` and
  `dag/lean_names_upstream.json`: neither new declaration exists.
- Related `abelianRigidification`, `poincare.*pullback`, `pullback.*poincare` searches:
  found the recorded parameter-pullback helper and polarization-calculus formulas;
  none constructs source-axis transport or states the present theorem.

Validation: `scompile.py NJ lem-sfb-dual-isogeny-degree <module>` compiled both the
sandbox probe and final library module cleanly (8.3 s and 19.3 s). No warnings or errors
were reported. Both auto-implicit options are disabled. The definition has actual data;
the only theorem proof is `sorry`.

## Second reading by NJ

The dispatcher forbids starting another agent; this is a separate rereading by the same
worker, with the original JSON and final Lean source open, not a claim of independent review.
The maintainer's independent delivery review remains required.

Rechecked each binder against the node: both original abelian varieties and both normalized
dual data occur, u is an isogeny, and uDual is a homomorphism in the reversed direction.
Checked the two whiskerings: A ◁ uDual acts in the second coordinate, while u ▷ DB.dual
acts in the first. Checked the rigidification equation's domain and order: pull back i,
then trivialize the target family, to get exactly the supplied source-family trivialization.
The source-axis helper first composes inverse images, then uses preservation of the unit,
then the original rigidification, without introducing any auxiliary hypothesis.
Both conclusions are present, and degree unfolds to the same coordinate-algebra finrank
specified by the node. No separability, algebraic closedness, positivity of dimension, or
perfection binder appears. No mismatch was found and no node fields beyond lean changed.
