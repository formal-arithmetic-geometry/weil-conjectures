## Worker report

Q124, stage 2, 2026-10-24. The module
`Sheaf.AlgebraicGeometry.KummerFixedSharpChart` states
`AlgebraicGeometry.exists_kummer_fixed_sharp_chart` with the sole postponed proof
`sorry`. It supplies no new definitions. The accepted stage-1 statement and split
are unchanged; only the item's `lean` field changes.

The inherited BLOCKED ending concerned a stage-1 assignment. The current standing
brief §0 explicitly distinguishes that from stage 2. The current queue lists this
item at stage 2, and its live node has no Lean record. Q69's report explicitly says
stage 1 only. There is no released repair note for this item.

Hypotheses and clauses, with the node and Lean open:

| Node text | Lean rendering |
| --- | --- |
| Locally Noetherian fs log schemes X,Y | `X Y : FineSaturatedLogScheme.{u}`; this existing structure contains local Noetherianity and an fs étale log structure. |
| A morphism f | `f : EtaleLogHom X Y`, including its actual section maps and structural compatibility. |
| Kummer étale | `_hkummer : f.IsKummer` and `_hetale : f.IsLogEtale`. |
| A geometric point x, y=f(x) | `Ω : Type u`, `[Field Ω] [IsAlgClosed Ω]`, `t : Spec (.of Ω) ⟶ X.scheme`; the target point is the actual composite `t ≫ f.base`. |
| Given chart a:P→M_Y on Y | `a` takes values on the identity étale object, and `_ha : Y.logStructure.IsChart ... a`. |
| P sharp fs | `_hfs : IsFineSaturatedMonoid P`; `_hsharp : ∀ p, IsUnit p → p = 1`. Multiplicative 1 is additive 0. |
| Given chart induces P≃characteristic at y | `_hchar` is bijectivity of the actual germ followed by `Associates.mk`, the recorded quotient by units. A bijective monoid homomorphism is an isomorphism; this is not an unrelated choice of identification. |
| Pointed étale neighbourhood U→Y of y | `U : Y.scheme.Etale` and `u` in the geometric fiber at `t ≫ f.base`. |
| Pointed étale W→X×_Y U | `W : X.scheme.Etale`, its point `w`, and `k : W.left ⟶ U.left` with `hk : k ≫ U.hom = W.hom ≫ f.base`. The relative arrow is the actual `pullback.lift W.hom k hk.symm`, asserted étale. `w.left ≫ k = u.left` makes it pointed over the induced point. |
| Sharp fs monoid Q | Existential `Q : Type u`, its `CommMonoid` structure, `IsFineSaturatedMonoid Q` and `∀ q, IsUnit q → q = 1`. |
| Chart b:Q→M_W | `b` takes values in the existing log sheaf on W; `X.logStructure.IsChart W b` tests the pulled-back structure. |
| Q≃characteristic at x | Bijectivity of `fun q ↦ Associates.mk (germ t W w (b q))`, using the canonical identification of the pointed étale log stalk with the original stalk. |
| Injective h:P→Q | `h : P →* Q` and `Function.Injective h`. |
| Every q has a positive multiple in h(P) | `∀ q, ∃ (d : ℕ) (p : P), 0 < d ∧ q ^ d = h p`. |
| a restricted to U | `aU` is forced equal to the original sheaf's restriction along `U ⟶ Scheme.Etale.mk (𝟙 Y.scheme)`, composed with a. |
| b∘h=f_W^flat(a restricted to U) | `∀ p, b (h p) = f.sectionMap U W k hk (aU p)`. This is equality of log sections, not only characteristic classes. |
| h^gp injective | `hg` is forced equal to `Algebra.GrothendieckGroup.lift ((Algebra.GrothendieckGroup.of).comp h)`; `Function.Injective hg`. |
| Finite cokernel | `Finite (Algebra.GrothendieckGroup Q ⧸ hg.range)`. |
| Annihilated by n>0 invertible on U | One `n : ℕ` with `0 < n`, `∀ y : U.left, IsUnit (n : U.left.presheaf.stalk y)`, and every cokernel class raised to n equals 1. The same integer is used throughout; invertibility is on the base U. |
| Étale scheme comparison | `c` maps into the pullback of `chartToSpec U aU` and `Spec.map (MonoidAlgebra.mapDomainRingHom ℤ h)`; its first projection is k and second is `chartToSpec W b`, and `Etale c`. These two equations uniquely characterize the canonical comparison. |
| No extra finiteness, strict locality, log regularity, reducedness or flatness | No such hypothesis appears. In particular neither `IsFinite f.base` nor flatness of the underlying morphism is required. |

Using W as an étale X-object does not strengthen the statement: the node's
W→X×_Y U followed by the base change of the étale U→Y is étale over X.
Conversely our relative arrow and its pointedness are explicitly included.
The two auxiliary existential maps aU and hg are fixed by equalities to their
canonical constructions; c is fixed by its two projections. None is arbitrary
replacement data. The identity point in `_hchar` is the actual lift of y, with
identity right arrow. All universes and variables are explicitly bound.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: `FineSaturatedLogScheme`,
  `EtaleLogHom` (especially `sectionMap`), `EtaleLogStructure.IsChart`,
  `EtalePrelogStructure.germ`, `EtaleLogStructure.characteristic`.
- `Sheaf.AlgebraicGeometry.KummerLogMorphism`: `EtaleLogHom.IsKummer`.
- `Sheaf.AlgebraicGeometry.FSLogSmoothEtale`: `EtaleLogHom.IsLogEtale`,
  `EtaleLogStructure.chartToSpec`; read also `FSLogChart`, its comparison,
  group map and cokernel. The fixed-P statement uses these same canonical
  constructions directly rather than an equality between monoid carrier types.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.lift`, `pullback.fst`, `pullback.snd`.

All the recorded dependency signatures and docstrings were read, including the
Mathlib étale and pullback declarations. There is no dependency repair or new node.
The available proof dependencies are imported privately: equivariant sharp charts,
fs face sharpening, differential generators, divisible-unit lattice extension,
and Kato lattice chart realization. The recorded module
`Sheaf.AlgebraicGeometry.LogSmoothCompositionStrictBaseChange` does not exist in
the live published source (`scompile.py --source` reports "Module source unavailable").
Its import was omitted after the wrapper's server confirmation reported the same
missing object file. The other unstated proof nodes are also omitted. They are
not statement prerequisites, and their proof steps remain in the theorem docstring.
Mathlib proof dependencies on étale open immersions and base change are provided
by the public étale import. No live file or tool was edited.

Source reading: opened the local ILO PDF, VI 2.2--2.3 and 3.7(a), printed
pp.72--75, and XVI Proposition 3.6.3/Lemma 3.6.4, printed pp.252--253.
The latter keeps a prescribed torsion-free base chart and uses the inverse-image
monoid; the Kummer argument in the accepted split makes it sharp. The seven
accepted proof steps are reproduced completely in the declaration docstring.
WANTED inherited from Q69: Stix 2002 §3.1.4 and Kato's original Theorem 3.5;
we use ILO's explicit lattice reconstruction rather than silently invoking a
stronger prescribed-chart assertion from the standard-cover citation.

Edge cases checked before writing and again against the signature:

- Empty X has no t, so the pointed assertion is vacuous.
- Trivial log structures force the sharp characteristic charts to be trivial;
  the comparison reduces to the ordinary étale local map. No positive rank is imposed.
- Identity morphisms allow h=id, zero cokernel and n=1.
- The standard d-root chart, including a unit twist, has finite cokernel Z/d;
  positive powers and an invertible annihilator are retained. A p-root chart in
  characteristic p is excluded by log étaleness, not by an added characteristic
  hypothesis. There is no n=0 loophole.
- Nonreduced schemes and arbitrary underlying Kummer étale maps remain allowed.
- A geometric point away from a closed point is allowed: no closedness or strict
  locality restriction occurs.

Searches (all performed through the authorized wrapper or read-only rg):

- `msearch.py ... leanfinder "Kummer log etale morphism has compatible sharp charts refining a prescribed base chart"`:
  eight ordinary standard-étale algebra hits; their returned signatures do not
  mention log structures, sharp characteristic monoids or fixed charts.
- `msearch.py ... loogle "FSLogChart, IsLogEtale, IsKummer"`: zero hits,
  unknown Mathlib identifier FSLogChart (the project interface is already used).
- `msearch.py ... grep "[Kk]ummer.*[Cc]hart|[Ss]harp.*[Cc]hart"`:
  zero Mathlib hits.
- `msearch.py ... leansearch "A Kummer log etale morphism admits sharp compatible charts extending a fixed chart at a geometric point"`:
  eight ordinary étale/formally unramified hits; read their returned types.
- `rg` in `lean/WeilConjectures` for the item id and logarithmic sharp-chart
  names: no exact statement. Broader Kummer hits concern coefficient-sheaf,
  number-field, Tate-twist and ordinary étale Kummer theory, different objects.
- `rg` in `lean/Sheaf/AlgebraicGeometry` for sharp and Kummer charts: found
  `LogRegularSharpChart` (requires log regularity, only one scheme),
  `VeryTameEquivariantSharpChart` (equivariant single-scheme chart),
  `KatoLatticeChartRealization` (different input lattice and general nonsharp chart),
  and `KummerStrictLocalStandardModel` (finite strict-local covers, a consumer).
  None states the fixed-chart refinement. The existing definitions are reused.
- Exact proposed-name searches in Mathlib, `dag/lean_names_upstream.json`,
  `lean/WeilConjectures` and `lean/Sheaf`: no collision.

Validation: scompile.py compiled both the sandbox and intended library module
cleanly (2.0 s and 2.1 s), no diagnostics. Only the theorem's proof is postponed.
No STATEMENT-DISPUTED finding, statement correction, or new/dependency module.

## Second reading by Q124

Author self-check, not an independent reviewer: the dispatcher explicitly prohibits
starting another agent; the maintainer supplies the independent reading.
I reopened the full accepted node and final Lean file and checked each row above.
In particular the finite cokernel is the whole quotient, not just its torsion
subgroup; the one positive annihilator is invertible on U, not merely on W;
the prescribed a is restricted by the sheaf's actual map; log compatibility is
literal equality; and both geometric lifts commute with k. The chart comparison
is determined by its scheme projections. The formulation as an X-étale W is
mathematically equivalent to the relative étale neighbourhood, which is also
asserted explicitly. There are no extra regularity, finite-morphism, locality or
underlying-flatness hypotheses. All seven source proof steps remain available
in the docstring. The first compile exposed an identity-arrow elaboration in
the restriction map; it was replaced with explicit `Category.comp_id U.hom`.
No mathematical clause changed. The only removed import names a proof module
absent from the live source, as recorded above.
