## Worker report

The delivery states `lem-trf-monoscheme-finite-chart-components` in
`Sheaf.AlgebraicGeometry.MonoschemeFiniteChartComponents`. Its four public theorems
partition the node's clauses into topology, algebra, localization, and realization.
Every theorem has proof `by sorry`, with the corresponding complete natural-language
argument and source in its docstring. No definition, dependency module, or new DAG
node is needed. Only the item's `lean` record changes.

The source was read in ILO, Travaux de Gabber, Exposé VIII, printed pp.98--100
(PDF pp.104--106), and pp.103--104 (PDF pp.109--110). In particular, 3.1.4
identifies the generic stalk with the monoid group completion, 3.1.10(ii) gives
the unique maximal generalization and component decomposition, 3.2.2 gives
localization-compatible gluing, and 3.2.4 gives the common dense torus. The domain
input is the embedding in the group algebra used in the proof of 3.2.12(ii).
The current blueprint unit `sec-trace-formula/sk-i-curve-zero/_section.md` was
also read; this item is an auxiliary node, not the unit's own statement.

Hypotheses and objects:

- The field is `(k : Type u) [Field k]`, with no restriction on characteristic.
- The fine monoscheme with finite affine cover is `(M : Fine.{u})`.
  `Fine.finiteCover` includes the finite-cover condition and permits `n = 0`.
- Torsion-freeness is precisely `(hM : M.IsTorsionFree)`, the recorded predicate
  on the group completions of all monoid stalks.
- `realization k M` is the recorded gluing `k[M]`, and `realizationToBase k M`
  is its specified structure morphism to `Spec k`.
- Monoid notation follows the dependencies: multiplication means the node's
  addition, `1` means its `0`, and `∏ i, p i` means its `a = ∑ i, p_i`.
- An affine chart is represented intrinsically by `U : AffineOpens M` (or
  `U : ComponentAffineOpens C`). Its monoid is
  `M.space.presheaf.obj (op U.1.1)` in the latter notation. This is the actual
  chart monoid P: sections on the whole monoid affine spectrum are P by
  3.1.3--3.1.4. A `Chart` with presentation monoid `c.monoid` determines such an
  affine open using `c.fine` and `c.iso`; the iso identifies this intrinsic
  monoid with `c.monoid`. Thus quantification covers every chart and every
  generating tuple, without choosing an extra presentation or an atlas.

Clause matching for `finite_chart_components`:

- `Finite M.space` states finiteness of the underlying space.
- `Finite (ConnectedComponents M.space)` states finiteness of its components.
- `∀ x, ∃! η, η ⤳ x ∧ ∀ z, z ⤳ η → z = η` gives the unique maximal
  generalization of every point, using the topological specialization relation.
- For each recorded `ToricComponent M`, `IsClopen` of the fiber of
  `ConnectedComponents.mk` makes the piece clopen; `IsGenericPoint C.genericPoint`
  of that fiber identifies it with the points specialized from its generic point.
  Together with uniqueness, this is exactly `{x : η(x) = η}` in the node.
- `IsIrreducible` and `ConnectedSpace` of this same fiber assert irreducibility
  and nonempty connectedness. `ConnectedSpace` includes nonemptiness.
- Equality of the range of these fibers with `irreducibleComponents M.space`
  states maximality as irreducible components. They are already the connected
  components by their definition as fibers of the component quotient.
- `∀ U, ∃ C, ∀ x ∈ U.1, ConnectedComponents.mk x = C.component` places every
  monoid affine chart entirely inside one component.
  Because `hM` supplies the torsion-free field of `ToricComponent` for every
  connected-component class, no component is omitted by using this type.

Clause matching for `finite_chart_components_algebra`:

- The first multiplicative equivalence identifies the generic stalk itself with
  the dependency's `C.lattice`, which is its group completion. Its equality
  `e.toMonoidHom = Algebra.GrothendieckGroup.of` fixes the canonical map and
  asserts that this stalk already is a group.
- `∃ r, Nonempty (C.lattice ≃* Multiplicative (Fin r → ℤ))` asserts a finite
  integral basis, equivalently a finitely generated torsion-free abelian group.
- For every component chart, its group completion has an equivalence to that
  same lattice, with `e (GrothendieckGroup.of p) = degree C U p`. The recorded
  `degree` is the germ map followed by the canonical completion, so this fixes
  the canonical identification rather than merely asserting abstract isomorphism.
- `IsDomain (MonoidAlgebra k ...)` is the chart algebra domain conclusion.
- A tuple `(p : Fin n → ...)` generates precisely when
  `Submonoid.closure (Set.range p) = ⊤`. Under that condition,
  `Algebra.adjoin k (Set.range (fun i ↦ MonoidAlgebra.of k _ (p i))) = ⊤`
  states exactly that its monomials generate the chart k-algebra.

Clause matching for `finite_chart_components_localization`:

- The same `C`, chart, finite tuple, and generating condition are explicit.
- `Algebra.faceLocalization ... (Submonoid.powers (∏ i, p i)) = ⊤`
  says that P[a^-1] is the entire chart group completion. The preceding
  canonical completion equivalence identifies this with `L_eta`.
- The existential `e : Localization.Away (MonoidAlgebra.of k _ (∏ i, p i))
  ≃ₐ[k] MonoidAlgebra k C.lattice` is the asserted k-algebra isomorphism.
- Its value on `IsLocalization.mk'` with numerator `e^q` and denominator
  `(e^a)^m` is `MonoidAlgebra.of ... (degree q * degree a ^ (-(m : ℤ)))`.
  This is exactly `e^(q-ma)`. The denominator carries the explicit powers
  membership witness. For `m = 0` the formula specifies its restriction to k[P].
- The Spec map of `MonoidAlgebra.mapDomainRingHom k (degree C U)` has range
  `(PrimeSpectrum.basicOpen (MonoidAlgebra.of k _ (∏ i, p i))).1`, exactly
  the asserted `D(e^a)` in this chart.
- This Spec map followed by `realizationι` equals the single recorded
  `torusEmbedding k C`, so every chart realizes the same open subscheme.
- The final quantified equality of ring homomorphisms says explicitly that
  these degree-induced algebra maps commute with every affine restriction
  `M.space.presheaf.map (homOfLE h).op`. The fraction formula uniquely extends
  those maps to the inverted monomials; thus it records compatibility with
  localization gluing, as well as the equality of the resulting scheme maps.

Clause matching for `finite_chart_components_realization`:

- `IsReduced (realization k M)` is reducedness of X.
- `LocallyOfFiniteType (realizationToBase k M) ∧ QuasiCompact (...)` is the
  dependency's exact finite-type predicate, which is this conjunction.
- `Finite (ConnectedComponents (realization k M))` states component finiteness.
- `Nonempty (IsColimit (Cofan.mk ... (fun C ↦ componentι k C)))` states the
  actual coproduct decomposition with the recorded component realizations
  `componentRealization k C = (componentOpen k C).toScheme` and their canonical
  inclusions. These are the realization pieces of the node.
- The equivalence with `ConnectedComponents (realization k M)`, together with
  the equality of each inclusion range with the corresponding quotient fiber,
  says these are exactly the connected components, with neither missing nor
  repeated pieces.
- `IsClosed (componentOpen k C : Set ...)` supplies closedness; openness is
  part of its existing `Opens` type. Thus the coproduct is clopen.
- `IsIntegral (componentRealization k C)` gives integral components.
- `IsOpenImmersion (torusEmbedding k C)`, `Nonempty (torus k C)`, and
  `IsIrreducible (Set.range ...)` give the nonempty irreducible torus open.
- `closure (Set.range (torusEmbedding k C)) = Set.range (componentι k C)`
  gives density exactly in the indicated component. Together with the chart
  range and map equalities above, this is the common dense D(e^a) assertion.
- `IsEmpty M.space → IsEmpty (realization k M) ∧ IsEmpty (ConnectedComponents ...)`
  explicitly includes the empty monoscheme, empty scheme, and zero components.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.MonoschemeToricRealization`:
  `AlgebraicGeometry.Monoscheme.Fine`, `Fine.IsTorsionFree`, `Chart`,
  `AffineOpens`, `ToricComponent`, `ComponentAffineOpens`,
  `ToricComponent.genericPoint`, `ToricComponent.lattice`, `degree`,
  `realization`, `realizationToBase`, `realizationι`, `componentOpen`,
  `componentRealization`, `componentι`, `torus`, `torusEmbedding` and its
  chartwise characterization `existsUnique_torusEmbedding`.
- `Sheaf.AlgebraicGeometry.FineFanBlowup`:
  `AlgebraicGeometry.FineFan.IsFine`, `stalk`, `germ`, and the affine monoid
  spectrum/localization sheaf underlying the preceding notions.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, `ConnectedComponents`.
- `Mathlib.Topology.Irreducible`: `IsIrreducible`, `irreducibleComponents`;
  `Mathlib.Topology.Sober`: `IsGenericPoint`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced` and
  `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, with
  `QuasiCompact` from its imported quasi-compactness module, as recorded in the node.
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`, using its
  ring structure and `IsLocalization.mk'` from the ring localization imports.
- `Algebra.faceLocalization` is the exact existing construction from
  `Sheaf.TraceFormula.FaceLocalizationFs`, publicly available through the
  recorded fan dependency; it is not defined anew.

Proof-only imports retain the recorded finite-free PID, affine unique-sums,
monoid-algebra domain, and basic-open/evaluation inputs. Spectrum prime topology
and affine reducedness are already imported by the statement dependencies.
`lem-trf-monoid-prime-minimal-neighborhood` has no Lean record or Mathlib match,
so it is named in the proof docstrings but has no import to add at this stage.
It is a proof dependency only and is not needed to type this statement.

Searches for an existing statement:

- `msearch.py leanfinder`, query `fine torsion free monoscheme finite charts
  integral components dense torus group algebra`: 8 hits, including `IsIntegral`
  and its generic algebraic-geometric consequences; no monoscheme result.
- `msearch.py loogle`, query `"MonoidAlgebra", "IsDomain"`: 2 hits, the
  additive and multiplicative domain instances from unique sums/products;
  these are the node's algebraic proof input, not the full statement.
- `msearch.py grep`, query `Monoscheme|toric|dense.*torus` in
  Mathlib/AlgebraicGeometry: 0 hits.
- `msearch.py leansearch`, query `finite fine torsion free monoscheme components
  generic stalk lattice dense torus realization`: 8 hits, including
  `genericPoints.finite`, `Module.basisOfFiniteTypeTorsionFree'` and general
  scheme integrality/finite morphism facts; no full statement.
- `rg` of `Monoscheme|monoscheme|finite_chart_components` and the node id in
  `lean/WeilConjectures`, and of the prospective theorem name in the upstream
  name index: no duplicate statement.
- `rg` of `finite_chart_components|dense.*torus|torusEmbedding|chartGroup` in
  `lean/Sheaf/AlgebraicGeometry`: existing realization definitions and
  `ToricRealizationFiniteType.lean` were read. The latter is a rational-field
  theorem with smooth-action/product clauses and lacks the node's finite monoid
  space, canonical completion, arbitrary-generator algebra and fraction-map
  clauses. It is not the same statement and cannot serve as an existing match.

Edge cases checked: empty monoscheme and cover; zero components; a rank-zero
lattice; the trivial monoid generated by an empty list; `n = 0`, where the
product is `1`, and localization away from `e^1 = 1`; denominator exponent
`m = 0`; monoids with units; nonsharp and nonsaturated fine monoids; disconnected
monoschemes; arbitrary field characteristic. No nonemptiness, sharpness,
saturation, separatedness, or positive-rank assumption was added. Every universe
and variable is explicitly bound, with `autoImplicit false`.

No statement correction or disputed statement was necessary. Server `scompile.py`
compiled the final module cleanly in both sandbox and library module modes.

## Second reading by Q49

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
