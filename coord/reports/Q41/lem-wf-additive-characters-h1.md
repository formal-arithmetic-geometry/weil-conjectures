## Worker report

Group Q41, item lem-wf-additive-characters-h1, stage 2. The delivered module is
`lean/Sheaf/Paper/AdditiveCharactersH1.lean`, main declaration
`AlgebraicGeometry.exists_additiveCharactersH1`. The theorem has `sorry`; all six
supporting definitions contain real data. No statement correction or disputed
statement is needed. The node copy changes only `lean`.

Source read: current blueprint `main-20261015`,
`blueprint/sec-purity-real-sheaves/sk-p-real-rankone/lem-wf-additive-characters-h1.md`
and its proof, equation (3.2), (3.3), and the concluding Frobenius formula. The old
source recorded on the node agrees with the current text for this assertion.

Hypotheses and objects, individually:

- The standing finite base field is `(k₀ : Type u) [Field k₀] [Finite k₀]`.
- A scheme over it is `{U₀ : Scheme.{u}}` and `p : U₀ ⟶ Spec (.of k₀)`.
- Geometric connectedness is `[GeometricallyConnected p]`.
- Separatedness is `[IsSeparated p]`.
- Finite type is `[LocallyOfFiniteType p] [QuasiCompact p]`, the usual scheme
  finite-type condition. Neither smoothness nor properness is imposed.
- The geometric base change `U` is the published `p.geometricFiber`, by definition
  the pullback along `Scheme.specAlgebraicClosure k₀`. Its model projection is
  `p.geometricFiberProj`. There is no arbitrary substitute for either map.
- The geometric point is `{Ω : Type u} [Field Ω] [IsSepClosed Ω]` and
  `t : Spec (.of Ω) ⟶ p.geometricFiber`.
- The geometric fundamental group is an arbitrary model `G : Type u` with
  `[Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]`,
  the actions on the fibres of all finite étale covers, and
  `[IsFundamentalGroup (Scheme.FiniteEtale.fiber t) G]`. This follows the
  recorded FUNDAMENTAL GROUP convention, rather than substituting an arbitrary
  profinite group. These structures express the chosen fundamental-group model.
- The coefficient prime is `(l : ℕ) [Fact l.Prime]`; its adic integers are
  `ℤ_[l]` with the existing valuation topology. No non-characteristic hypothesis
  or finiteness/discreteness assumption on the fundamental group is added.
- Connectedness of `U₀` and of `p.geometricFiber` is supplied explicitly by
  `GeometricallyConnected.connectedSpace_of_subsingleton` applied to `p`, and
  `GeometricallyConnected.geometrically_connectedSpace` applied to the defining
  pullback square of `p.geometricFiber`. They are not extra hypotheses.

Conclusions and all their clauses:

1. `adicCharacterResidueSheaf X l n` is the existing constant sheaf on the small
   étale site with coefficient group `ULift.{u+1} (ZMod (l^n))`. The `ULift`
   supplies exactly the `AddCommGrpCat.{u+1}` universe required by the recorded
   cohomology API; its canonical additive equivalence is `AddEquiv.ulift`.
2. `adicCharacterH1 X l n` is actual `Sheaf.H` of that sheaf in degree one.
   It does not define cohomology as a character group or as a custom surrogate.
3. `adicCharacterResidueReduction l n` uses `ZMod.castHom`, transported by
   `AddEquiv.ulift`, for reduction from exponent `n+1` to `n`.
   `adicCharacterH1Reduction` applies `constantSheaf.map` and `Sheaf.H.map` to
   this very coefficient homomorphism. There is no unspecified transition map.
4. `adicCharacterH1Limit` is the `AddSubgroup` of all tuples whose adjacent
   coordinates agree under those transitions. Its intersection of
   `AddMonoidHom.eqLocus` subgroups gives the concrete group inverse limit.
5. The displayed isomorphism is `∃ e : Additive (G →ₜ* Multiplicative ℤ_[l]) ≃+
   adicCharacterH1Limit p.geometricFiber l`. The multiplicative wrapper is only
   the standard encoding of additive-valued characters on a multiplicative
   fundamental group; pointwise addition supplies the additive group.
6. The first conjunct fixes the canonical isomorphism, coordinatewise: the
   existing finite torsor-monodromy bijection of `(e b)_n`, evaluated on `g`
   and lowered from `ULift`, equals `PadicInt.toZModPow n (b g).toAdd`.
   Thus `e` is exactly the reduction/classification map in the source proof,
   rather than an existential isomorphism with an unrelated normalization.
7. The second conjunct states pointed-pullback naturality for every connected
   scheme `V`, geometric point `v`, fundamental-group model `GV`, morphism
   `f : V ⟶ p.geometricFiber`, and path
   `τ : pullback f ⋙ fiber v ≅ fiber t`. The monodromy of
   `adicCharacterH1Pullback f l n ((e b)_n)` at `g : GV` is the residue of
   `b (fundamentalGroupMap τ GV G g)`. Finite monodromy is a bijection, so
   this is exactly the coordinatewise naturality square for the canonical
   comparison. The path is the standard datum specifying the pointed map;
   all such paths are quantified. The source `V` need not descend to `k₀`.
8. `adicCharacterH1Pullback` is `Etale.cohomologyMap` followed by `Sheaf.H.map`
   of the canonical `Scheme.upperStarConstantSheafIso`; hence its source and
   target are the specified constant-coefficient cohomology groups.
9. The last conjunct quantifies every arithmetic fundamental-group model `G₀`
   at `t ≫ p.geometricFiberProj` and every
   `s : Scheme.FiniteEtale.weilGroup p (t ≫ p.geometricFiberProj) G₀` of degree
   `Multiplicative.ofAdd 1`. For every character `b` it supplies a continuous
   character `b'`. For every geometric `g`, it asserts the existence of `h`
   whose canonical image in `G₀` is `s.val.1⁻¹ * image(g) * s.val.1`, with
   `b' g = b h`. The canonical image is specifically `fundamentalGroupMap`
   of `pullbackFiberIso p.geometricFiberProj t`, not a free embedding. The
   geometric fundamental group embeds in the arithmetic one in this setting,
   so this expresses exactly `b'(g) = b(s⁻¹gs)` using separate group models.
10. Finally `(e b')_n = adicCharacterH1Pullback
    p.geometricGaloisFrobenius.hom l n ((e b)_n)` for every `n`.
    This is pullback by the actual geometric Galois Frobenius on the geometric
    base change, the cohomological action in the source; combined with the
    preceding clause it states Frobenius equivariance with exactly the
    inverse-conjugation convention in (3.2).

Dependency declarations read and used:

- `def-weil-pbc-etale-cohomology`: imported
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, recorded
  `AlgebraicGeometry.Etale.cohomology` and `rightDerivedGlobalSections`.
  Its `lean.note` explicitly permits the source's `CategoryTheory.Sheaf.H`
  spelling for abelian sheaf cohomology; that is the spelling used here.
- `def-wf-weil-group`: imported
  `WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup`, specifically
  `AlgebraicGeometry.Scheme.FiniteEtale.weilGroup` and `weilGroupDeg`.
  Read their constant-cover action and `geometricFrobenius` convention.
- `def-weil-l-adic-numbers`: its Mathlib match supplies `Padic`, `PadicInt`,
  the valuation topology, and `PadicInt.toZModPow`.
- The existing finite classifier used to express normalization is
  `AlgebraicGeometry.Scheme.EtaleTorsor.sheafHEquivContinuousMonoidHom`, in
  `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor` (signature and
  full torsor-monodromy docstring read, also confirmed through `scompile.py
  --source`). It is the existing canonical construction, not a new postponed
  helper theorem. The proof of our item still follows the node's
  `lem-wf-finite-constant-h1-pi1` for additivity, coefficient naturality and
  Weil-descent equivariance; those are not falsely attributed to this bare
  finite-level `Equiv` declaration.
- Canonical geometry and pointed maps use `Scheme.Hom.geometricFiber`,
  `geometricFiberProj`, `geometricGaloisFrobenius`,
  `Scheme.FiniteEtale.pullbackFiberIso` and `fundamentalGroupMap` from the
  existing GeometricFiber/GeometricFrobenius and Restriction modules.
- Pullback uses `AlgebraicGeometry.Etale.cohomologyMap` from
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`
  and `Scheme.upperStarConstantSheafIso` from ConstructibleSheaf.Defs.
- `WeilConjectures.Mathlib.NumberTheory.Padics.RingHoms` supplies existing
  `PadicInt.continuousMonoidHomEquiv` and its naturality, as well as the residue
  API for the node's proof dependency
  `lem-exc-padic-residue-universal-property`. It proves the group-theoretic
  half only; it is not an existing match for this cohomological theorem.

The six helpers belong to this node's specified tower, transition maps and
canonical pullback. They are listed in `lean.declarations` with source/blueprint
docstrings, as authorized for helpers of the owning notion. No absent independent
notion is introduced and no dependency record is replaced.

Edge cases checked before the final statement:

- `n=0`: coefficients are `ZMod 1`, the trivial group. The zeroth cohomology
  coordinate in this degree-one tower is trivial, and adjoining it to the
  tower indexed by `n≥1` adds no datum or constraint, as the node's proof states.
- `l=2` is allowed. `l=0` and `l=1` are excluded precisely by primality.
- `l=char(k₀)` is not excluded; constant finite étale sheaves and their
  torsor classification remain the correct objects in this case.
- Trivial geometric fundamental group is allowed. The statement then says
  the compatible H¹ tower is trivial, rather than presupposing a nonzero class.
- The empty scheme is not inadvertently included: geometric connectedness
  and the specified geometric point imply nonemptiness. No extra rational
  point, splitting of the arithmetic fundamental-group sequence, or fixed
  choice of degree-one lift is required. The formula quantifies every lift.
- `V=U`, identity morphism, and identity fibre path are included in the
  naturality clause. Finite/discrete source-group shortcuts are not used.
- Scheme and point universes are explicitly bound (`u`), coefficients are
  canonically lifted to `u+1`, and all group models are in the fibre-functor
  universe prescribed by the existing API. No extra universe equality is
  imposed to force cohomology into a smaller category.

Searches made (no full existing match):

- `msearch.py ... leanfinder "Continuous characters into p adic integers are
  compatible finite constant etale H1 classes"`: eight results, including
  adic additive-character equivalences (the adic integers are their source),
  cyclotomic characters and BDeRham; none is this cohomological statement.
- `msearch.py ... loogle "PadicInt.lift, PadicInt.toZModPow"`: `lift_self`,
  `lift_spec`, `lift_unique`, and related residue ingredients; their source
  signatures were read. These do not contain the étale comparison.
- `msearch.py ... grep "continuousMonoidHomEquiv|etale.*H1|adic.*character"`:
  thirteen ingredient/unrelated hits; no comparison with actual étale H¹.
- `msearch.py ... leansearch "First etale cohomology of finite constant abelian
  sheaves corresponds naturally to continuous adic characters"`: eight
  generic group-H¹, continuous-cohomology and adic-character results, no match.
- `rg` on the upstream source, including the item id, found
  `PadicInt.continuousMonoidHomEquiv` in the project's Padics/RingHoms and its
  use in RealSheaves/FundamentalGroup. Full declarations were read: only the
  inverse limit of finite characters is present, not cohomology or the
  asserted Frobenius comparison. `FundamentalGroup/Torsor` supplies the
  canonical finite dictionary and was reused.
- `rg` of `lean/Sheaf` and `dag/lean_names_upstream.json` found no declaration
  for this entire statement or duplicate `adicCharacterH1` helper. Existing
  node `cor-galois-abelian-h1` was read to identify the upstream finite
  dictionary; it is not duplicated or restated in this delivery.

The docstring gives the full six-step natural-language proof from the node:
finite coefficient naturality; compatible residues and their unique lift;
continuity of residues; continuity of the lifted character using norm bounds;
inverse identities, additivity and pointed naturality; and exactly inverse
conjugation for Frobenius. Stage 2 supplies its statement only.

Validation: the complete module passed the prescribed `scompile.py` wrapper in
both the private sandbox and the library-path confirmation. Its sole final
style diagnostic was a line exceeding 100 characters; that line has been split,
and the exact final source is checked again by the required delivery dry run
and delivery. The node signature is synchronized verbatim with the file.
There are no auxiliary theorem holes or hollow data.

## Second reading by Q41

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer review fix (2026-10-18)

The live library already has this node's notions, tagged `lem-wf-additive-characters-h1`, in
`WeilConjectures.AlgebraicGeometry.FundamentalGroup.AdditiveCharacters`: `Scheme.EtaleTorsor.constantZModPow`
(the constant sheaf `ULift (ZMod (l^n))`), `constantZModPowReduction`, `sheafHOneLimit` (the compatible
families) and `continuousMonoidHomPadicEquiv` (the canonical bijection, with level-`n` class equal to the class
of the reduction, `sheafHEquivContinuousMonoidHom_continuousMonoidHomPadicEquiv`). The delivered
`adicCharacterResidueSheaf`, `adicCharacterH1`, `adicCharacterResidueReduction`, `adicCharacterH1Reduction` and
`adicCharacterH1Limit` restated them (H4). They are removed. The theorem now states, about the existing
bijection: additivity in every coordinate, pointed pullback naturality, and the Weil-group Frobenius formula
with pullback along the geometric Galois Frobenius. The helper `adicCharacterH1Pullback` stays, retyped on
`constantZModPow`. The hypotheses, the naturality clause and the Frobenius clause are unchanged in substance.
The normalization clause is no longer needed because the map is the canonical declaration itself.
