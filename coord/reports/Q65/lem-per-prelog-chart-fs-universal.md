## Worker report

The module `Sheaf.AlgebraicGeometry.PrelogChartFsUniversal` states
`AlgebraicGeometry.prelogChart_fs_universal`. Its sole postponed proof is that theorem.
All its helper definitions contain actual constructions; no object or map is chosen
from an existence theorem. The natural-language statement is unchanged.

Sources read: ILO VIII 3.1.17, printed p.101 (PDF p.107), defining saturation by
positive powers in the group completion; X, proof of Theorem 3.5, Step 6, printed
p.164 (PDF p.170), describing the integral saturated chart of the fs product.
The displayed universal property and its six-step proof are the existing DAG's
agent-supplied formulation, not a purported quotation from ILO. I also read the
current blueprint `lem-per-artin-gabber-affine-curve` statement and proof, especially
Step 3, for the recorded ancestor. This delivery does not change that unit.

Hypothesis and construction correspondence:

- `A : Type (max u v)`, `[CommRing A]`, `[IsNoetherianRing A]` express the
  Noetherian commutative ring. `S : Type v`, `[CommMonoid S]`, `hS : Monoid.FG S`
  express the finitely generated commutative monoid. `β : S →* A` is the prelog
  homomorphism to the multiplicative monoid of the ring. Multiplicative notation
  uniformly replaces additive notation in the node, with powers replacing multiples.
- `prelogChartMonoid S` is `FineFan.saturation` of the image of the canonical
  `Algebra.GrothendieckGroup.of`. The existing saturation uses the submonoid
  closure of the positive-root subset. That subset is already closed under products:
  if `x^n` and `y^m` are in the image, then `(xy)^(nm)` is also in it. It contains
  the identity. Thus this is exactly the root subset in the statement, with no
  torsion-freeness assumption. `prelogChartInclusion S` is the actual composite
  through the image and its canonical inclusion into saturation. `hP : Monoid.FG
  (prelogChartMonoid S)` is exactly the additional finite-generation hypothesis.
- `MonoidAlgebra ℤ S` and `MonoidAlgebra ℤ (prelogChartMonoid S)` are the rings of
  finite monomial sums. `prelogChartCoefficientAlgebra β` uses
  `MonoidAlgebra.lift ℤ A S β` to give the action `z^s ↦ β(s)` on `A`.
  `prelogChartSaturationAlgebra S` uses `MonoidAlgebra.mapDomainRingHom` on the
  canonical inclusion for the other action.
- `prelogChartRing β` is the actual `TensorProduct (MonoidAlgebra ℤ S) A
  (MonoidAlgebra ℤ (prelogChartMonoid S))` under those two actions. Its
  `prelogChartRingCommRing` is the canonical tensor multiplication. The local
  `letI` terms occur only inside construction definitions, never in the theorem
  signature. There are no arbitrary algebra structures supplied as hypotheses.
  `[IsNoetherianRing (prelogChartRing β)]` is precisely the assumed Noetherianity of B.
- `prelogChartCoefficient β` is `a ↦ a ⊗ 1` via
  `Algebra.TensorProduct.includeLeftRingHom`. `prelogChartMonomial β` is
  `p ↦ 1 ⊗ z^p` via `includeRight` and `MonoidAlgebra.of`.
  `prelogChartBeta β` transports this chart to global functions using the inverse
  of `Scheme.ΓSpecIso`. `prelogChartProjection β` is `Spec.map` of the coefficient
  map and has ordinary `Spec A` as target, with no target log structure imposed.

Conclusion and naturality correspondence:

- The existential `L` is an `EtaleLogStructure` on exactly `Spec (.of
  (prelogChartRing β))`. The existential presheaf map `η` and
  `IsAssociatedLogPresentation (prelogChartBeta β) L η` specify exactly the
  associated log structure of that chart, by the dependency's sheafification
  universal property and structural formula. This determines the object up to its
  unique chart-preserving isomorphism; it is not an arbitrary choice of log data.
- `hN` and `hfs : L.IsFineSaturated` assert the locally Noetherian fs conclusion.
  `prelogChartLogScheme β L hN hfs` bundles this exact spectrum and log structure.
  No extra conclusion about log regularity or torsion-freeness is asserted.
- Tests range over `T : FineSaturatedLogScheme.{max u v}`. This recorded type
  includes exactly the local Noetherianity and fs conditions required of tests.
  The source-chart universe `v` is independent of the common scheme/site universe
  `max u v`; `MulEquiv.ulift.symm` supplies the explicit canonical transport into
  the existing associated-log interface. No equality between the original source
  universes is required.
- `prelogChartSection β L η` is the associated `P` chart precomposed with the
  canonical map `S → P`. `prelogChartExtract` sends a recorded `EtaleLogHom` to
  the pair consisting of `F.base ≫ prelogChartProjection β` and its actual
  `sectionMap` on global log sections composed with that `S` chart. Thus the
  forward map is prescribed, not an arbitrary equivalence or unconstrained map.
- `prelogChartCompatible β T q` says exactly
  `α_T.comp q.2 = q.1.appTop.comp (ΓSpecIso A).inv.comp β`. These are the
  scheme map `v`, monoid map `λ`, and equation `α_T λ = v♯ β` in the node.
  Global log sections are evaluated at `op (Scheme.Etale.mk (𝟙 T.scheme))`.
- `Function.Injective prelogChartExtract` and its exact `Set.range` equal to
  `{q | prelogChartCompatible β T q}` express bijectivity onto precisely that set.
  In particular every compatible pair has one and only one log morphism.
- For `h : EtaleLogHom T' T`, `h.CompEq F H` is the dependency's exact equality
  with a composite, including both scheme and log maps. The following equality
  of extracted pairs identifies extraction of the composite with
  `prelogChartPullbackPair h` of the extracted pair. The latter uses `h.base`
  and the actual map on global log sections. This is the naturality square for
  log morphisms. Inverses are natural too because the forward maps are injective.
- For every base open `U : (Spec (.of A)).Opens`, the final `Set.BijOn` restricts
  the same map to log morphisms whose scheme image lies in the inverse-image open
  of C and compatible pairs whose scheme map lands in U. A scheme map to an open
  subscheme is exactly a map to the ambient scheme with image in that open; with
  the restricted target log structure the same factorization describes log maps.
  Thus this is the universal property on `C ×[Spec A] U`, identified with that
  inverse-image open, without assuming U is affine. Together with the preceding
  naturality square applied to open restrictions of T, it includes restricting
  a given pair and log map to `v⁻¹(U)`. The forward map remains the identical
  chart-pullback formula; injectivity forces agreement of the inverse. U empty
  and U the entire spectrum are included.

Dependencies used:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: `EtaleLogStructure`,
  `EtaleLogStructure.IsFineSaturated`, `FineSaturatedLogScheme`, `EtaleLogHom`,
  `EtaleLogHom.CompEq`. Read the full signatures and docstrings in the recorded
  module, including their relative étale test maps and composition equations.
- `Sheaf.AlgebraicGeometry.AssociatedLogUniversalStalks`: `associatedLogPresheaf`,
  `associatedLogIota`, `IsAssociatedLogPresentation`; its existence/stalk theorem
  is available for the future proof. Read the recorded module in full.
- Mathlib `TensorProduct` and its canonical ring structure in
  `Mathlib.RingTheory.TensorProduct.Basic`; the module tensor definition, bilinear
  map, lift and uniqueness signatures were checked against the recorded leaf.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec` and `Spec.map`; the full signatures
  and docstrings were read. `Mathlib.AlgebraicGeometry.GammaSpecAdjunction` gives
  `Scheme.ΓSpecIso` and the recorded affine adjunction for the future proof.
- Added the already landed definition node `def-trf-fine-fan-blowup` to statement
  dependencies to cite its existing `FineFan.saturation` and `FineFan.intoSaturation`.
  The module imports and uses those actual definitions, rather than recreating them.
  No new node or dependency repair module is needed.
- The proof-only import `Sheaf.AlgebraicGeometry.IntegralChartLogificationThickening`
  supplies the recorded arbitrary-map chart bijection for the future proof. Its
  theorem signature/docstring and `integralChartCompose` were read. The sections
  saturation lemma has no recorded Lean declaration in the read base, so there is
  no module for that proof dependency to import yet. It is not needed to type
  this stage-2 statement. Its DAG dependency remains intact.

Edge cases checked before drafting:

- The trivial monoid gives P trivial and B canonically A, the ordinary affine
  adjunction with the trivial log structure.
- An arbitrary finitely generated group, including a finite cyclic torsion group,
  is permitted as S. There is no nontriviality, sharpness, domain or
  torsion-freeness binder. The proof docstring uses uniqueness of the extension
  on group generators, not uniqueness of nth roots.
- For the monoid generated by an idempotent e, group completion kills e; B
  imposes `β(e)=1`, exactly the condition that cancellation imposes on any map
  into the log sections of an fs test. Nonintegral S is not silently excluded.
- For the numerical monoid generated by 2 and 3 the saturation is N; the chart
  map is the inclusion into its saturation, not an assumed identity or injection
  of the original S. No arbitrary roots in the ring are selected.
- B equal to the zero ring gives the empty spectrum; the statement has no
  `Nontrivial` hypothesis and still quantifies over the empty test scheme.
- Empty and whole base opens are included; general base opens need not be affine.
  A test's global log sections are not assumed finitely generated.

Searches actually run:

- `msearch.py leanfinder`, query: "Integralization and saturation of a monoid chart
  represents maps from fine saturated log schemes". Eight hits, led by
  `Scheme.Hom.normalizationDiagram`, its map, and ordinary scheme partial-map
  constructions. The returned signatures concern scheme normalization, not log
  charts or the required bijection; no exact match.
- `msearch.py loogle`, query: `"GrothendieckGroup", "saturation"`. Zero hits.
- `msearch.py leansearch`, query: "Universal property of saturation of monoid charts
  in logarithmic schemes". Eight hits: `Subalgebra.saturation`, its inclusion and
  membership lemma, monoid localization, and site-precoverage saturation. The
  returned signatures give different saturation notions; no exact statement match.
- `msearch.py grep`, query `rootClosure|saturation`, subdirectory `GroupTheory`.
  Zero hits. A further grep of `LogStructure|LogScheme|FineSaturated` in
  `AlgebraicGeometry` also had zero hits.
- `rg` over both project Lean roots for `prelog-chart-fs`, `prelogChart`, `fsChart`,
  and saturation/chart combinations found the existing generic chart and
  `FineFan.saturation` definitions, but no copy of the item's theorem. The
  explicit node-id grep in `WeilConjectures` had no hit. A final `rg` of
  `prelogChart|PrelogChart|fs_universal` in both source roots and
  `dag/lean_names_upstream.json` had no hit.

No statement fault or STATEMENT-DISPUTED claim was found. The helpers are part of
this node's specified construction and canonical arrow, rather than new independent
notions. No existing node besides the item's Lean record and the permitted addition
of a landed statement dependency is changed.

Validation: `scompile.py` compiled the complete module in sandbox and library
module modes without errors or warnings. `deliver2.py --no-push` then printed
`OK (dry run)` after compiling and passing the server preflight. The source has
exactly one `sorry`, in the named main theorem; all 16 public declarations are
listed in `lean.declarations`. Only `lean` and the permitted `stmt_deps` addition
change in the node copy.

## Second reading by Q65

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
