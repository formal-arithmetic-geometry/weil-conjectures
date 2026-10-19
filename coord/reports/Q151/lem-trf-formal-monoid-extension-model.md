## Worker report

The module `Sheaf.RingTheory.FormalMonoidExtensionModel` states
`Algebra.formalMonoidExtension_model`, with its sole theorem proof `sorry`.
All other declarations have real data. The tensor algebra and all its chart and
localization maps are the canonical constructions, not arbitrary maps with
assumed properties. The theorem has two implications, one per formal-model
hypothesis, joined by a conjunction. Thus the same data may support either or
both hypotheses, and neither model is silently omitted.

Clause-by-clause correspondence:

- The commutative, nonzero, Noetherian local ring `(A,m)` is
  `(A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]`.
  Mathlib's `IsLocalRing` includes `Nontrivial`; a redundant explicit
  `[Nontrivial A]` was removed after the compiler's overlapping-instance warning.
  Throughout, `m` is `IsLocalRing.maximalIdeal A` and the residue field is
  `IsLocalRing.ResidueField A`.
- The fs monoids `R,Q` are independent types in universes `v,w`, with
  `[CommMonoid R]`, `[CommMonoid Q]` and the exact recorded predicate
  `AlgebraicGeometry.IsFineSaturatedMonoid` in `_hR,_hQ`.
  They are written multiplicatively, while the sharp monoids are tagged
  `Additive` to use `AddMonoidAlgebra`. This changes notation only.
- `h : R →* Q` is the given homomorphism; `_hgp` is bijectivity of the actual
  group-completion map
  `GrothendieckGroup.lift ((GrothendieckGroup.of (M := Q)).comp h)`.
  No extra injection, rank equality, or condition on the induced sharp groups
  is assumed.
- `α : R →* A` is the chart. Its unit preimage `G` is the actual submonoid
  `(IsUnit.submonoid A).comap α`. `Localization G` is the universal monoid
  localization. For the integral monoids in this statement it identifies
  canonically with the specified fraction submonoid `{r-g}` of `R^gp`.
  `chartSharpMonoid α` is `Additive (Associates (Localization G))`.
  `Associates` quotients by the whole group of localized units. For this face
  that group is exactly `G^gp`, so this is precisely `S=R_G/G^gp`, not a quotient
  of the original unlocalized monoid.
- `a : Multiplicative (chartSharpMonoid α) →* A` is the stated monoid map.
  `ε : GrothendieckGroup R →* Aˣ` is the character. `localizedUnitChart α` extends
  `α` by Mathlib's localization lift, with the unit proof supplied by membership
  in `G`. `unitChartGroupMap α` is the canonical localization-to-group map.
  `_hα` quantifies over every element of `Localization G` and says exactly
  `α_extended(r)=ε(r)*a(bar r)`, with `bar r=Associates.mk r` and the type tags.
- In case (a), the antecedent of the first implication quantifies over `n : ℕ`
  and an isomorphism from
  `CompletedLocalModel (IsLocalRing.ResidueField A) (chartSharpMonoid α) n`
  to `AdicCompletion (maximalIdeal A) A`.
  `CompletedLocalModel` is the existing completion of `k[S][t]` at
  `(m_k,[s]:s≠0,t)`; `m_k=0` for this field. The following universal equation
  sends every completed basis monomial to the completion of `a(s)`.
  The coefficient inclusion through the isomorphism supplies the coefficient
  field. No independently chosen coefficient homomorphism is postulated.
- In case (b), the second antecedent quantifies over a commutative local `V`,
  `p : ℕ`, `IsCohenRing p V`, an isomorphism of its residue field with `A/m`,
  `n`, the actual `θ` in the existing completed model, and a quotient-ring
  isomorphism to the completion of `A`. The condition
  `θ - p ∈ completedLocalModelBoundaryIdeal V S n` is exactly the stated
  congruence modulo nonzero monomials AND all old variables. The universal
  equation includes `Ideal.Quotient.mk (Ideal.span {θ})`, so compatibility is
  imposed in the actual quotient. There is no extra assumption of characteristic
  zero on `A` and no exclusion of `θ=p` or `θ=p-t`.
- `monoidChartTensor α h` constructs
  `A ⊗[MonoidAlgebra ℤ R] MonoidAlgebra ℤ Q` as a bundled commutative ring.
  Its two algebra structures are induced by `MonoidAlgebra.lift ℤ A R α` and
  `MonoidAlgebra.mapDomainRingHom ℤ h`; no ambient algebra is left unspecified.
  `monoidChartTensorBase` is the canonical left inclusion and
  `monoidChartTensorMonomial` is the right inclusion of basis monomials.
- `q : Ideal (monoidChartTensor α h)` and `[q.IsPrime]` are the specified prime.
  `_hq` is its contraction equality with `maximalIdeal A` along the canonical
  base map. `B` is literally `Localization.AtPrime q`.
  `localizedTensorMonomial` is the actual chart map to that localization.
- The new face `F` is the preimage of the unit submonoid along that local chart
  map. The same `chartSharpMonoid` construction gives
  `T=Q_F/F^gp`. `localizedTensorBoundary` is the ideal spanned by precisely the
  chart monomials whose images are NOT units, hence exactly `([q]:q∉F)B`.
- The conclusion in each case is expanded by `HasExtendedFormalMonoidModel`.
  It gives a commutative `D`, explicitly nontrivial and regular local, with
  `IsAdicComplete (maximalIdeal D) D`, and an isomorphism
  `ResidueField D ≃+* ResidueField B`. The latter is exactly `κ(q)`.
- For case (a) it gives an actual ring equivalence
  `AdicCompletion (maximalIdeal B) B ≃+* CompletedLocalModel D T 0`.
  The zero-variable polynomial presentation is canonically `D[T]`.
  Its defining ideal is `(m_D,[v]:v≠0)`. The zero-variable boundary ideal has
  exactly the nonzero `T`-monomials as generators, since `Fin 0` is empty.
- For case (b) it gives the actual relation `η` in that same completed model,
  its coefficient-compatible stratum isomorphism
  `(H ⧸ completedLocalModelBoundaryIdeal D T 0) ≃ₐ[D] D`, and BOTH the conditions
  that the reduction of `η` lies in `maximalIdeal D` and that it does not lie
  in `(maximalIdeal D)^2`. It gives an actual ring equivalence from the completed
  `B` to `H/(η)`. The monomial and completion ideals are mapped by the actual
  quotient map. In particular the conclusion does not demand the false stronger
  congruence `eta_bar-p ∈ m_D²`.
- `IsAdicPairEquiv` says that the specified ideals are equal under `Ideal.map`
  of the equivalence, and explicitly requires `Continuous` for the equivalence
  and its inverse in the two indicated `Ideal.adicTopology` structures.
  On the source these are defined by `m_B` extended to its completion; on the
  target by the defining model ideal extended to the completion and, in case
  (b), mapped to the quotient. These are exactly the completion topologies.
  The distinguished source ideal is `J` extended to the completion, and the
  target ideal is the actual generated monomial ideal, not just its closure.

Dependency declarations and source reading:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` and
  `isNoetherianRing_iff_ideal_fg`, read at lines 190--207.
- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup` reexports
  `AlgebraicGeometry.IsFineSaturatedMonoid` from
  `Sheaf.AlgebraicGeometry.LogRegularPair`; read its full definition at lines
  137--148, using the canonical Grothendieck group and root saturation.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion` and
  `IsAdicComplete`; read their compatible-sequence and complete/Hausdorff
  definitions. `Algebra` supplies the completion ring and coefficient algebra.
- `WeilConjectures.RingTheory.CohenRing`: `IsCohenRing`, read through
  `scompile.py --source` because this current published source is absent in the
  older upstream checkout. Its conjunction includes primality, domain, DVR,
  maximal ideal `(p)`, and adic completeness. No replacement was needed.
- The tensor dependency is a Mathlib leaf with no `lean` record. Its recorded
  `mathlib_match` is `TensorProduct`, `mk`, `lift`, `LinearMap.rTensor`; read the
  full signatures and docstrings in `Defs`, `Basic`, `Map`. The ring tensor
  structure is from `Mathlib.RingTheory.TensorProduct.Basic`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`,
  with the local ring and residue field clauses from the recorded dependency.
- For `def-weil-regular-scheme`, its record explicitly retains the ring clauses
  supplied by `Mathlib.RingTheory.RegularLocalRing.Defs`:
  `IsRegularLocalRing` extends `IsLocalRing` and `IsNoetherianRing`, with the
  stated maximal-ideal generator condition. Read that class and the recorded
  scheme declaration `AlgebraicGeometry.IsRegularScheme`; only the ring clause
  is used here. There is no unusable dependency requiring repair.
- Added the already-landed `lem-trf-log-regular-saturation-normality` to
  `stmt_deps` to cite the actual owning node of `CompletedLocalModel`,
  `localModelCompletionIdeal`, and `completedLocalModelBoundaryIdeal`.
  Their whole source and docstrings were read. These are reused unchanged;
  the theorem about their normality is not an assumption of this theorem.
- Imported the already-stated proof dependencies: formal monoid dimension,
  completion regularity, local completion quotient, power series coefficient
  regularity, regular local localization, kernel parameters, and upstream adic
  completion Noetherianity. Mathlib proof-dependency matches use the polynomial
  regularity, completion completeness, cotangent and PID-basis APIs.
  `lem-trf-fs-face-sharpening` currently has neither a Lean record nor a Mathlib
  match, so there is no module to import for that proof-only dependency. Its
  intended argument remains in the theorem docstring; the statement uses
  Mathlib's actual localization and unit quotient without relying on a choice
  from this postponed theorem.

Edge cases checked before and after writing:

- `n=0` uses `Fin 0`, so it contributes no spurious parameter generator.
- Trivial `S` or `T` produces an empty nonzero monomial list. The construction
  remains a coefficient completion, with boundary ideal zero.
- A field `D` is possible in case (a); in case (b) `m_D\m_D²` is empty for a
  field, so no invalid zero-dimensional parameter witness is asserted.
- `R` or `Q` may have nontrivial units or torsion in their unit groups. Only
  their fs predicates and the given group-completion isomorphism are assumed;
  no torsion-free condition on the whole group is added.
- The sharp map may drop rank (the node's blowup example), so no equality of
  face groups or injectivity of sharp group maps appears.
- The identity chart `A=k[[x]]`, with its genuine monomial `x`, remains covered;
  compatibility maps the full monomial into the completion, not its reduction.
- The mixed congruence permits old linear parameters such as `θ=p-t`, and the
  output only requires the exact parameter condition, as in the repaired node.
- No prime of the tensor ring is assumed to exist; the theorem applies to every
  given prime over `m`. Its localization is then nonzero.
- Input rings and monoids use independent universes. The tensor's carrier is
  in `max u w` (the base ring's universe `v` does not enlarge a tensor's quotient
  carrier). Coefficient and output existential universes are large enough to
  contain the constructed rings; no universe equality is imposed.

Searches for an existing statement and notions:

- `msearch.py ... leanfinder "Formal models of completed local monoid algebra
  base change along a map inducing an isomorphism on group completions"`:
  eight hits, including monoid algebra pushouts, tensor equivalences and local
  coefficient maps. None computes the localized completed monoid models or
  their distinguished ideals.
- `msearch.py ... loogle '"AddMonoidAlgebra", "AdicCompletion"'`: zero hits.
- `msearch.py ... grep 'formalMonoid|formal_monoid' RingTheory`: zero hits.
- `msearch.py ... leansearch "Completed local model of a fine saturated monoid
  algebra base change"`: eight hits about localization and base change,
  including `IsLocalization.tensor`, `tensorRight` and unramified base change.
  No exact completed local-model assertion.
- `rg` in the upstream `WeilConjectures` and side `lean/Sheaf` for fine saturated
  monoids, formal monoid rings, face localization and sharpening located the
  existing model rings and unit quotient APIs described above. The older
  completed-chart monomial helper is specialized to equal ring/monoid universes;
  this module uses the raw canonical algebra-map expression rather than copying
  it or restricting universes. No separate monomial helper is introduced.
- `grep -rn` for the item's blueprint id in upstream `WeilConjectures`: no hit.
- `rg` over Mathlib, upstream and `lean/Sheaf` for every proposed declaration
  name: no existing declaration with any of these names.
- The local ILO PDF was read after `pdftotext`, at VI 1.6 and VIII 3.1.1--3.1.5.
  The two models and localization/sharpening definitions agree with the node.
  Its independently supplied base-change proof is retained in all fourteen
  steps of the theorem docstring.

No statement correction, new definition node, dependency repair, or disputed
statement is needed. The construction helpers only unpack objects and the
conclusion expressly introduced by this item, and are listed in `lean.declarations`.
All writes were confined to the sandbox and all compilation used `scompile.py`.

## Second reading by Q151

This is the author's second reading, not an independent review; the dispatcher
brief assigns independent review to the maintainer. I reopened the node and
read the module against each clause in the correspondence above. I checked
especially: the character equality quantifies over the entire localization;
`C` is formed with the two prescribed maps, not arbitrary algebra instances;
`F` is computed after prime localization; `S,T` are unit quotients of actual
localizations; and the conclusion identifies generated ideals under the actual
ring equivalence. The mixed reduction uses a `D`-algebra stratum equivalence and
retains membership and nonmembership separately. Both continuities are explicit.
The two branches are implications under the same chart data, not alternatives
chosen without preserving the model case. The initial implementation's redundant
nontrivial binder was removed, and the monomial formulas were expanded using
canonical algebra maps to avoid a duplicate universe-specialized helper.
No remaining mathematical mismatch was found. Definitions contain no `sorry`,
and the only postponed theorem has the node's full proof plan in its docstring.
