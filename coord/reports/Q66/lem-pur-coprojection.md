## Worker report

`Sheaf.Paper.PurityCoprojection` states `AlgebraicGeometry.ProEtale.purity_coprojection`.
The proof is `sorry`; its docstring carries all five DAG proof steps and their dependencies.
Two definition helpers only specialize existing constructions and express the canonical
map through its counit equation. Neither defines new tensor products, pullbacks,
exceptional functors, coefficient rings, or constructibility conditions.
The node's statement and dependency lists are unchanged. No dependency record is changed.

Hypothesis and clause matching:

- The finite purity setting is `P : WeilConjectures.PurityFiniteSetting.{u}`. Its fields
  provide the prime characteristic, positive finite-field exponent, algebraic closure k,
  distinct coefficient prime, finite subextension of the coefficient closure, and positive
  level. `P.Ring` is the existing quotient `Padic.coefficientExtensionRing`; `P.Coefficient`
  is precisely its standard ULift for module sheaves. No ramification divisibility or
  twist assumption is made.
- The separated finite-type k-schemes Z and W are the `Over (Spec (.of P.field.k))`
  instances with `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on their
  structure morphisms. `i.IsOver` makes i a k-morphism; `IsClosedImmersion i` states
  precisely the closed-immersion hypothesis.
- The existing proper-map `HasCompactification` instance supplies a default
  compactification of i. This excludes no immersion: every closed immersion is proper.
  There is no extra compactification, dimension-bound, or ambient exceptional-adjunction
  hypothesis. All counits and projections use the same default compactification.
- The small pro-etale site is `Scheme.ProEt.topology W` (respectively Z), with object
  universe u+1 and morphism universe u, and coefficients `ModuleCat.{u+1} P.Coefficient`.
  This is the fixed-scalar presentation canonically equivalent to modules over A_W.
- K is an arbitrary derived object subject to `_hK : purityCoprojectionConstructible P W K`.
  That helper is exactly the recorded `intrinsicFiniteTorsionConstructible` applied through
  `finiteCoefficientIntrinsicRealization W P.Ring` applied on derived categories. It imposes boundedness and constructibility,
  without finite Tor amplitude on K.
- L belongs to the recorded finite-Tor category by `_hL : finiteTorConstructibleProEtaleModule
  ... W L`. `_hInv` supplies `TensorInvertibleData` for the existing derived tensor and
  coefficient unit. Its `inverse` M belongs to that same finite-Tor category, and its
  `iso` is L tensor M isomorphic to the unit. The reverse tensor identity follows by
  symmetry and is not an extra hypothesis.
- `purityCoprojectionProperty` asserts an isomorphism e from
  `Ri^!.obj (K ⊗ L)` to
  `Ri^!.obj K ⊗ Li*L`, using the same `rightDerivedUpperShriek` on both sides.
  Its defining composite is exactly `sfFiniteExceptionalFixed` at the default
  compactification; spelling the upstream owner directly avoids repeatedly unfolding
  the entire composite during elaboration.
  Pullback is the existing `upperStar.leftDerivedFunctor`, identified with the exact
  module pullback used by the recorded intrinsic finite operations.
- Canonicity is the equation
  `PF(GK,L) ≫ F.map e.inv ≫ eps(K ⊗ L) = eps(K) ⊗ id(L)`.
  The PF is `projectionMap`, namely `projectionMapOfCompactification` at the default
  compactification, the third component of
  `finiteExchangeProjection` in def-exchange-projection. The counit is
  `rightDerivedUpperShriekCounit`, the explicit comparison-site transport of the
  ordinary etale counit. Invertible PF identifies e.inv uniquely as its exceptional
  transpose. Tensor equivalence with M identifies e with the right-adjoint comparison
  induced by projection with M, as in the node's last proof step. Thus this specifies
  the canonical map, not an unspecified endpoint isomorphism.
- The bounded-below witnesses for K and K tensor L are existential conclusions inside
  the property, used only to type the actual relative counits. They add no input
  hypothesis. Quasi-compactness of W supplies bounded-below preservation of the
  ordinary etale adjoint through the published finite-coefficient instance; no ambient pro-etale adjunction is postulated.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, `.Ring`,
  `.Coefficient`, and their existing coefficient instances.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and `.topology`.
  The morphism-properties node is explicitly a convention/collection with no declaration;
  its specified Mathlib `IsClosedImmersion`, `IsSeparated`, `LocallyOfFiniteType`,
  `QuasiCompact`, and `Scheme.Over` are used directly.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `Scheme.intrinsicFiniteTorsionConstructible`.
- `Sheaf.Paper.FiniteTorAmplitudeProEtaleModule`:
  `WeilConjectures.finiteTorConstructibleProEtaleModule`, whose definition is the
  recorded intrinsic finite-Tor condition through canonical coefficient realization.
- `Sheaf.Paper.Pur9Invertible`: `AlgebraicGeometry.TensorInvertibleData`. This dependency
  records both the chosen inverse triple and the existence condition; the generic triple
  applies directly to the fixed-scalar derived tensor, without choosing K-flat models again.
- `Sheaf.Paper.DerivedPullbackTensorHom`: finite derived operations, read with their
  K-flat normalization. The fixed-scalar forms use the existing upstream derived tensor
  and derived inverse image in the upstream owning modules. The collection module
  combines old and finite-coefficient comparison branches, so only the matching finite
  operation owners used here are imported, as required by the duplicate-import repair
  instruction.
- `Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage`: the original recorded
  `sfFiniteExceptional`, its fixed-scalar form `sfFiniteExceptionalFixed`, and its
  intrinsic transport equivalence. The fixed-scalar form is literally Rnu_* followed by
  the ordinary etale exceptional adjoint and nu*. The upstream finite-coefficient
  `rightDerivedUpperShriek` is this same composite; its actual counit is
  `rightDerivedUpperShriekCounit`. `QuasiCompact.compactSpace_of_compactSpace aW`
  supplies the target compactness required by the existing etale bounded-below instance.
  This supplies the interface without additional hypotheses or dependency repairs.
- `Sheaf.Paper.ExchangeProjection`: I read `finiteExchangeProjection`, which uses
  exactly `projectionMapOfCompactification`; our counit equation uses that component.
  Importing the collection module forced the broken overlay module
  `LowerShriek.OpenImmersion.BaseChange` to import both legacy and finite-coefficient
  declarations of `upperStarIsoLowerStarInv`. Per the launcher duplicate-import repair
  instruction, the delivery imports its smaller upstream owning module
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection`
  directly, together with the matching finite-coefficient UpperShriek module. This
  supplies exactly the same canonical projection component, without unrelated exchange
  base-change constructions. The dependency record itself needs no mathematical change.
- All available proof-dependency modules are imported without `public` (and the Mathlib
  Yoneda, adjointification and unique-adjoint modules are available). The two proof nodes
  `lem-pur-derived-pullback-tensor-iso` and `fix-prop-projection-formula` have no Lean record
  in the supplied DAG, so there is no recorded module to import. They are proof-only
  prerequisites, not absent notions needed for this signature.

Edge cases checked before writing: i identity, empty Z, empty W, K zero, the coefficient
unit L, and shifted invertible units. The counit equation is the standard tensor mate in
all these cases; it never requires K to be finite-Tor. Level 1 is retained, as are arbitrary
positive levels and ramified E. Neither scheme dimensions nor nonemptiness are restricted.
The scalar lift changes the presentation, not the coefficient ring or the site universes.
No statement dispute or mathematical correction was necessary. The repair note for this
item is stage 1/resolved and asks to retain the existing statement; this delivery does so.

Searches made with `msearch.py Q66 lem-pur-coprojection`:

- LeanFinder: `An invertible tensor factor commutes with the constructible exceptional
  inverse image for a closed immersion` returned eight unrelated geometric/pullback hits;
  no exact statement.
- Loogle: `CategoryTheory.Adjunction.rightAdjointUniq, CategoryTheory.Adjunction.comp`
  returned zero hits. The generic unique-right-adjoint declaration exists and was read
  directly; it does not state the geometric result.
- Mathlib grep: `coprojection|coProjection|exceptional.*tensor|upperShriek` returned fifteen
  coproduct/distributivity hits, no exceptional co-projection.
- LeanSearch: `Exceptional inverse image co-projection formula for an invertible complex
  of sheaves` returned eight inverse-map/sheaf-equivalence hits, no match.
- Direct rg in upstream WeilConjectures and side Sheaf for the item id, `coprojection`,
  `coProjection`, `UpperShriek.*Tensor`, and `upperShriek.*tensor` found no pro-etale
  constructible theorem. The current framework has the canonical etale tensor mate and
  abstract invertibility lemma, but not this node on its small pro-etale constructible
  domain. The upstream exact-id search also found
  `Etale.derivedTensorRightCompRightDerivedUpperShriekIso` and
  `Etale.nonempty_iso_rightDerivedUpperShriek_derivedTensor_of_isInvertible` in
  `WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection`, together with
  `Adjunction.tensorRightCompIsoOfTensorIso` in the generic tensor-invertibility module.
  I read their complete signatures and docstrings: these are an ambient etale
  statement and an abstract-adjunction construction, respectively. The latter requires
  an adjunction on the categories provided to it, and cannot be applied to an
  unrestricted ambient pro-etale exceptional adjunction. Neither is an exact existing
  match for this constructible pro-etale node.
  The existing pro-etale relative counit and compact-support projection provide
  the exact canonical-map equation. No declaration named `purity_coprojection` or either
  helper exists in the upstream declaration index, source tree or side library.

## Second reading by Q66

The dispatcher explicitly forbids starting other agents and assigns independent review
to the maintainer. This is a second pass by the same worker, not independent review.
I reopened the node and module and checked each binder and the counit equation against
the five-step proof. K has only Dbc membership; L and its inverse both have Dctf
membership. The sites remain small pro-etale, and the exceptional operation remains the
recorded comparison composite. The iso has the node's direction; its inverse occurs in
the counit equation. Compactness and coefficient finiteness are derived from the stated
data. No source statement changed and no dependency record needed repair.

Compilation exposed incompatible imports of old and finite-coefficient versions of
`UpperLowerStar.Iso` and `Derived.Comparison`. I read their current server sources through
`scompile.py --source`, then selected the matching finite-coefficient upstream owners
for projection and exceptional counit, retaining the original exceptional dependency.
The narrower imports follow the dispatcher's prescribed repair for duplicate declarations.
No live library source or artifact was edited.

The kernel timeout was repaired by binding the existing functors F, G, Q and the
existing curried tensors once inside the definition body, then applying their `.obj`
and `.map` operations. The theorem signature contains no let binder. These are
ordinary aliases inside a definition, not alternate constructions or hypotheses;
the exact counit equation and the canonical projection remain unchanged.

Validation: `scompile.py Q66 lem-pur-coprojection` compiled the complete module in
sandbox coordinates (15.4 seconds) and its actual library module name (16.7 seconds),
with no errors or non-sorry warnings and without increasing any limit.
