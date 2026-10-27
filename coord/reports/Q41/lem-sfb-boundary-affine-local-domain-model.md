## Worker report

The module `Sheaf.AlgebraicGeometry.BoundaryAffineLocalDomainModel` states
`AlgebraicGeometry.exists_boundary_affine_local_domain_model` for a finite-type,
quasi-compact morphism `g : U ⟶ Y`, a locally Noetherian target, and a boundary
point `y`. It introduces the source point `x`, affine opens `V = Spec B` and
`W = Spec C`, the finite-type coordinate map `φ`, the points `p`, `q`, `r`, and
an explicit presentation `R ≃+* Localization.AtPrime (p/q)`. The existential
conjunction records every clause of the node: specialization and distinctness,
prime contraction and strict inclusion, the kernel of the map to the residue
field, the induced localization map and its fraction formula, nonzero
Noetherian local-domain and nonfield properties, maximal ideal and contraction,
and the canonical common subfield of the residue field identified with
`Frac(B/q)`, `κ(q)`, and `Frac(R)` by compatibility with the original map.

The hypotheses render as `[LocallyOfFiniteType g]`, `[QuasiCompact g]`,
`[IsLocallyNoetherian Y]`, and
`hy : y ∈ closure (Set.range g) \ Set.range g`. The affine conclusion is rendered
by `v : Spec B ≅ V.toScheme`, `w : Spec C ≅ W.toScheme`, membership hypotheses
`y ∈ V`, `x ∈ W`, and `W ≤ g ⁻¹ᵁ V`; the chart commutativity is the displayed
composition equality. Finite type is `φ.FiniteType`, Noetherianity is
`IsNoetherianRing B`, and specialization is `g x ⤳ y` with `g x ≠ y`.
The prime clauses use `PrimeSpectrum`, `asIdeal`, `Ideal.comap`, and strict ideal
inclusion. The local ring uses `Localization.AtPrime`, `IsLocalRing R`,
`IsNoetherianRing R`, `IsDomain R`, `¬ IsField R`, and the explicit maximal ideal
and contraction equations. The fraction-field clause uses `Subfield`,
`FractionRing`, `RingEquiv`, and the stated compatibility equations.

Dependency declarations used are: `AlgebraicGeometry.Scheme` and `Scheme.Hom`
(Mathlib.AlgebraicGeometry.Scheme); `AlgebraicGeometry.LocallyOfFiniteType`
and `AlgebraicGeometry.QuasiCompact` (Mathlib.AlgebraicGeometry.Morphisms.FiniteType
and QuasiCompact); `AlgebraicGeometry.IsLocallyNoetherian` and
`isLocallyNoetherian_of_affine_cover` (Mathlib.AlgebraicGeometry.Noetherian);
`AlgebraicGeometry.Spec` and `Spec.map` (Mathlib.AlgebraicGeometry.Scheme);
`IsNoetherianRing` (Mathlib.RingTheory.Noetherian.Defs);
`Localization.AtPrime`, `Ideal.ResidueField`, and `Ideal.Fiber`
(Mathlib.RingTheory.Localization.AtPrime.Basic); the residue-field notions
`Ideal.ResidueField`, `Ideal.ker_algebraMap_residueField`,
`Ideal.injective_algebraMap_quotient_residueField`,
`instIsFractionRingQuotientIdealResidueField`, `Ideal.ResidueField.ringHom_ext`,
and `Ideal.ResidueField.lift` (Mathlib.RingTheory.LocalRing.ResidueField.Ideal);
`AlgebraicGeometry.exists_specializes_of_mem_closure_range`
(WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact); and
`AlgebraicGeometry.Spec.residueFieldMap_residueFieldIso_hom`
(WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.PropertyC).

Edge cases checked: the strict inclusion `q.asIdeal < p.asIdeal` makes the
localized prime proper and nonzero, so the asserted ring is nonzero and not a
field; denominators lie outside the prime and hence map to nonzero elements;
`FractionRing` is used only for the domain quotients `B/q` and `R`; the
subfield condition explicitly excludes zero denominators; empty opens cannot
satisfy the required point memberships; and the statement allows arbitrary
universe `u` without identifying unrelated site universes.

Searches: `msearch.py leanfinder` for the complete affine local-domain/residue
field package (no complete match); `msearch.py loogle "Localization.AtPrime,
Ideal.ResidueField"` (individual Mathlib declarations only); `msearch.py grep
"AtPrime.*[Qq]uotient|[Qq]uotient.*AtPrime|boundary.*[Dd]omain" RingTheory`
(no complete match); `rg` over `lean/WeilConjectures` and `lean/Sheaf` for the
item and boundary-local-domain names (no existing declaration; nearby modules
are different statements). The source proof was read at Stacks Tag 0CM2 in
`literature/stacks-project/limits.tex`.

The module compiles cleanly with `scompile.py`; the theorem proof is the required
`sorry` and no definition contains postponed data.

## Second reading by Q41

Reading of the node `lem-sfb-boundary-affine-local-domain-model`, Stacks 0CM2
(`limits.tex`, first paragraph of the proof) and the module
`Sheaf/AlgebraicGeometry/BoundaryAffineLocalDomainModel.lean` side by side,
clause by clause (this replaces an earlier self-check; written by the
maintainer's second reader).

Hypotheses.
- $g:U\to Y$ of finite type [def-weil-finite-type-morphism]: `g : U ⟶ Y`,
  `[LocallyOfFiniteType g] [QuasiCompact g]`, the pair recorded by the
  dependency node. Same.
- $Y$ locally Noetherian [pqf-def-locnoeth]: `[IsLocallyNoetherian Y]`, the
  recorded Mathlib class. Same.
- $y\in\overline{g(|U|)}\setminus g(|U|)$, Zariski closure:
  `hy : y ∈ closure (Set.range g) \ Set.range g` in the topology of `Y`. Same.
- No further assumption; universes: `U Y : Scheme.{u}`, rings in
  `CommRingCat.{u}` (the universe of Γ of an open), no restriction.

Conclusion.
- $x\in U$, $V=\operatorname{Spec}B\ni y$, $W=\operatorname{Spec}C\subseteq g^{-1}V$,
  $W\ni x$: `x`, `V W` opens, `v : Spec B ≅ V.toScheme`,
  `w : Spec C ≅ W.toScheme`, `y ∈ V`, `x ∈ W`, `W ≤ g ⁻¹ᵁ V`. Same.
- $\varphi$ finite type inducing $g|_W$, $B$ Noetherian:
  `w.hom ≫ W.ι ≫ g = Spec.map (ofHom φ) ≫ v.hom ≫ V.ι`, `φ.FiniteType`,
  `IsNoetherianRing B`. Same (the square fixes φ by Spec full faithfulness).
- $z=g(x)$ specializes to $y$, $z\ne y$: `g x ⤳ y ∧ g x ≠ y`. Same.
- $\mathfrak p,\mathfrak r,\mathfrak q=\varphi^{-1}\mathfrak r$ represent
  $y,x,z$; $\mathfrak q\subsetneq\mathfrak p$: `V.ι (v.hom p) = y`,
  `W.ι (w.hom r) = x`, `V.ι (v.hom q) = g x`, `q.asIdeal = r.asIdeal.comap φ`,
  `q.asIdeal < p.asIdeal`. Same.
- $P=\mathfrak p/\mathfrak q$: `P.asIdeal = p.asIdeal.map (Ideal.Quotient.mk _)`.
- $\ker h=\mathfrak q$ for $h:B\to C\to\kappa(\mathfrak r)$:
  `RingHom.ker ((algebraMap C r.asIdeal.ResidueField).comp φ) = q.asIdeal`,
  κ(𝔯) = `Ideal.ResidueField` of def-weil-pbc-localization-at-prime. Same.
- $R=(B/\mathfrak q)_{P}$: `R` with `e : R ≃+* Localization.AtPrime P.asIdeal`
  and `a : B →+* R` pinned by `e ∘ a = algebraMap ∘ mk`; the transport along
  `e` loses nothing (all later clauses are stated through `e`, `a`, `ι`).
- ι embedding factoring $h$ by $(b+\mathfrak q)/(s+\mathfrak q)\mapsto h(b)/h(s)$:
  `hbar` pinned by `hbar ∘ mk = h`; `Function.Injective ι`, `ι ∘ a = h`, and
  `ι (e.symm (mk' b s)) = hbar b / hbar s` for all `b`, `s ∈ P.primeCompl`;
  since every element is an `mk'`, ι is the node's map, not an arbitrary one.
- $R$ nonzero Noetherian local domain, not a field: `hlocal : IsLocalRing R`,
  `IsNoetherianRing R`, `IsDomain R` (contains nontriviality), `¬ IsField R`.
- $\mathfrak m_R=(\mathfrak p/\mathfrak q)R$ with inverse image $\mathfrak p$:
  `maximalIdeal R = (P.map algebraMap).map e.symm`,
  `comap a (maximalIdeal R) = p.asIdeal`. Same.
- Subfield of quotients of $R$ in $L$, canonically and compatibly with $h$
  equal to $\operatorname{Frac}(B/\mathfrak q)=\kappa(\mathfrak q)$, hence
  $\operatorname{Frac}(R)$: `K : Subfield`, membership `t = ι b / ι c`, `c ≠ 0`;
  `eA : FractionRing (B⧸q) ≃+* K` with `eA (b̄) = h b`; `eκ : q.ResidueField ≃+* K`
  with `eκ (algebraMap B _ b) = h b`; `eR : FractionRing R ≃+* K` with
  `eR (b) = ι b`. Each equivalence is unique given its compatibility
  (fraction-ring / `Ideal.ResidueField.ringHom_ext` uniqueness), so they are
  the canonical identifications, not bare existence.

Edge cases: `U` empty gives an empty closure, the hypothesis is false and the
statement vacuous; `q = p` is excluded by `g x ≠ y`, which is what makes `R`
not a field; denominators `s ∉ P` have `hbar s ≠ 0`, so the division is the
field division in κ(𝔯). Examples: ℤ → ℤ[1/2] at y=(2) gives `R = ℤ_(2) ⊂ ℚ`.

Records: `lean.statement` equals the file's signature (whitespace-normalised
comparison). Plain imports `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
and `...EtaleTopologicalInvariance.PropertyC` are the recorded modules of the
proof_deps lem-sc-picard-closure-specialization and
lem-weil-pbc-spec-map-residue-field-naturality (required by brief-stage2 §3).
No pro-étale material; no definition; proof `sorry`; no line over 100 chars;
docstrings carry the source place, `(blueprint: …)` and the seven proof steps.
Searches: the parent `NoetherianImageBoundaryDvr.lean` states only the DVR
existence (`exists_dvr_of_mem_closure_range_not_mem_range`); rg in
`lean/Sheaf` for `Localization.AtPrime` with `ResidueField` finds no package of
this statement; the worker's Mathlib searches cover single clauses only.

Mismatches found: none in the Lean or the records. Changed: this section
(the earlier one was a self-check, H11).
