## Worker report

The module `Sheaf.AlgebraicGeometry.DerivedChowNeighbourhood` states
`AlgebraicGeometry.Scheme.exists_derivedChow_neighbourhood`, with its sole proof `by sorry`.
It defines no new notion. I read the node, all eight statement-dependency records and their
source declarations, and Stacks `more-morphisms.tex`, Tag 0CSJ, lemma-derived-chow,
including all six clauses and the proof. The node statement is unchanged.

Hypotheses and existential objects:

- The commutative ring is bundled as `A : CommRingCat.{u}`; no domain, nonzero,
  Noetherian, field or characteristic hypothesis is imposed.
- The scheme is `X : Scheme.{u}`, with its specified structural map `f : X ⟶ Spec A`.
  Using an explicit map is appropriate because the conclusion forms its fibre product.
- Separatedness is `[IsSeparated f]`. Finite presentation is exactly
  `[LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]`, following
  the morphism-conventions node's definition, rather than using local finite presentation alone.
- The point is `x : X`.
- The two `HasDerivedCategory.{w}` families select the common derived localization for
  every scheme module category and its localized open-site module categories. They are
  foundational category-size data, as in the recorded pseudo-coherence definition, not
  extra geometric or finiteness hypotheses. Both universes `u w` are explicit.
- `U : X.Opens` with `x ∈ U` is the open neighbourhood.
- `n : ℕ` represents precisely an integer at least zero. The projective scheme is
  `Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (n + 1))) A`, namely Proj of A's
  polynomial algebra in n + 1 homogeneous coordinates. The coordinate lift only places
  the finite coordinate set in the ring's universe; it does not change the dimension.
- `V` is an open of exactly that projective scheme. The canonical structure map is
  `Proj.projectiveSpaceOverAffineToSpec (ULift.{u} (Fin (n + 1))) A`.
- The ambient T is literally `pullback f` of that structure map, not an arbitrary scheme
  or a product over a different base. `Z : Scheme.{u}`, `h : Z ⟶ T`, `z : Z`, and
  `E : schemeDerivedCategory T` are the remaining existential witnesses.

Conclusion, clause by clause (P and T below are descriptive abbreviations only; the Lean
signature spells out the actual terms):

1. `IsClosedImmersion h`, `LocallyOfFinitePresentation h`, `QuasiCompact h`, and
   `QuasiSeparated h` say h is a finitely presented closed immersion, retaining all
   parts of the node's finite-presentation convention.
2. Writing b for the actual term `h ≫ pullback.fst f (...)`,
   `IsIso (b ∣_ U)` says the canonical map from b's inverse image of U to U is an
   isomorphism. `b z = x` retains the specified point above x.
3. Writing c for `h ≫ pullback.snd f (...)`, `IsClosedImmersion (c ∣_ V)` states
   the canonical closed immersion over V, on the full inverse image c⁻¹(V).
4. `b ⁻¹ᵁ U = c ⁻¹ᵁ V` is equality of the opens of Z, hence also of the associated
   open subschemes. `z ∈ b ⁻¹ᵁ U` explicitly retains containment of z in their common open.
5. The `Nonempty (... ≅ ...)` is an isomorphism in the actual derived category on the
   localized open site. Both sides use `SheafOfModules.overFunctor` at
   `pullback.snd f (...) ⁻¹ᵁ V`, the entire open X ×_A V in T. The right side starts
   with `(Modules.pushforward h).obj (SheafOfModules.unit (moduleRings Z.toRingedSpace))`,
   the ordinary h_*O_Z, and applies `DerivedCategory.singleFunctor ... 0` before
   restriction. Thus it is exactly `(h_*O_Z)[0]` restricted to that open. It does not
   substitute a cohomology-only equality or comparison only on U ×_A V. The over-site
   formulation is the existing restriction used in `Scheme.IsPseudoCoherent`; it is
   the canonical localized-site presentation of module sheaves on the open subscheme.
6. `IsPseudoCoherent T E` is precisely the dependency's scheme-local bounded-above
   finite-free condition. For every `j : ℤ` and every `t : T`,
   `t ∉ Set.range h → Subsingleton (↑(TopCat.Presheaf.stalk (H^j(E)).val.presheaf t))`
   states zero cohomology stalk off h(Z). An additive module is zero exactly when its
   carrier is subsingleton. Neither quasi-coherence nor boundedness of E is assumed
   separately. The cohomology is the actual `DerivedCategory.homologyFunctor`, in
   every integer degree.

Dependency declarations used (full signatures/docstrings read in their source):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory`, with the shared `SheafOfModules` carrier.
- `WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex`:
  `AlgebraicGeometry.Scheme.IsPseudoCoherent`, including both localization instance binders.
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage` supplies the recorded
  derived-direct-image module. Clause (5) itself explicitly uses ordinary pushforward
  in degree zero, as the source says; it does not replace that object by an arbitrary R h_*.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist` imports the project's
  projective-space construction: `AlgebraicGeometry.Proj.projectiveSpaceOverAffine` and
  `Proj.projectiveSpaceOverAffineToSpec`. These use the literal polynomial Proj from the
  dependency statement, rather than depending on an unstated identification of the
  integral-model base-change construction with polynomial Proj.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `IsSeparated`;
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
  The convention dependency fixes these existing notions and has no declaration of its own.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, via the project's existing scheme pullbacks.
- `Mathlib.AlgebraicGeometry.Restrict`: `AlgebraicGeometry.morphismRestrict` (`∣_`).
- `Mathlib.AlgebraicGeometry.Modules.Sheaf`: `Scheme.Modules.pushforward`;
  `Mathlib.Algebra.Category.ModuleCat.Sheaf`: `SheafOfModules.unit`.
- The declared proof dependencies having modules are imported as plain proof imports,
  including descent, Noetherian approximation, graph images, coherent pushforward,
  pseudo-coherence, K-flatness, pullback composition and standard projective charts.
  `lem-sfb-relative-flat-closed-kernel-base-change` has no Lean record or Mathlib match
  on the read base; it is only a future proof dependency and is not used to type this
  statement. No missing notion or unusable statement dependency requires a new module.

Edge cases checked before writing:

- n = 0 uses one homogeneous coordinate, so P^0 is retained; an empty coordinate
  type is never accidentally substituted for dimension zero.
- If X is empty, there is no x, and the universal theorem is vacuous as it should be.
  The zero ring case likewise has no point above its empty spectrum. Neither case is
  excluded by an added nonemptiness/nontriviality assumption.
- For a supplied x, the displayed equations ensure z exists and lies over x in the
  common open. No separate nonempty hypothesis on Z, U or V is added.
- A = any commutative ring, including non-Noetherian rings, is allowed. The proof's
  Noetherian approximation is not promoted to a hypothesis.
- The support quantifies over all integer degrees, including negative ones; the zero
  derived object passes the support condition, without making the prescribed kernel
  comparison vacuous.
- The product open in the comparison is the inverse image of V under T → P; no U
  restriction is present. This checks the precise source issue already noted by stage 1.
- No statement correction or `STATEMENT-DISPUTED` flag is necessary.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder` query: "A separated finitely presented scheme over a ring
  has a derived Chow neighbourhood with a pseudo coherent kernel supported on a closed
  graph". Eight hits: IsSeparated and its affine/local instances, Scheme.IsSeparated,
  Proj.isSeparated and diagonal facts. None includes the Chow data or derived kernel.
- `msearch.py ... loogle` query: `"IsPseudoCoherent", "IsClosedImmersion"`.
  Zero hits.
- `msearch.py ... leansearch` query: "Derived Chow lemma pseudo coherent complex
  supported on graph with open neighbourhood isomorphism and closed immersion into
  projective space". Eight hits: closed-immersion factorization/image characterizations,
  induction principles and a Proj open-immersion fact; no matching existence assertion.
- `msearch.py ... grep` query: `derived.?[Cc]how|[Cc]how.*[Nn]eigh|pseudo.?[Cc]oherent`
  in Mathlib's AlgebraicGeometry directory. Zero hits.
- `rg` for `derived.?[Cc]how|[Cc]how.*[Nn]eigh|lem-sfb-derived-chow-neighbourhood`
  in the project's `WeilConjectures`, `Sheaf` and upstream-name index finds only the
  different algebraic-space neighbourhood and transform-restriction modules.
  I opened `SpaceDerivedChowNeighbourhood.lean`: its theorem is in namespace
  `AlgebraicGeometry.AlgebraicSpace` and gives an etale scheme neighbourhood rather
  than the isomorphism b⁻¹(U) ≅ U required here. It cannot serve as this node's declaration.
- `grep -rn 'lem-sfb-derived-chow-neighbourhood'` in `WeilConjectures` gives no match.
  A separate full-name search for `exists_derivedChow_neighbourhood` finds only the
  algebraic-space namespace, so the proposed scheme full name is fresh.

Validation: the prescribed `scompile.py N7 lem-sfb-derived-chow-neighbourhood` compiled
both sandbox and library module forms cleanly (6.7 and 6.3 seconds), with no error or
unexpected warning. The first elaboration attempt required a `: Scheme.{u}` annotation
on the quantified ambient point type to disambiguate polymorphic pullback; the final
signature includes that annotation. All binders are explicit and `autoImplicit` is false.
The node's `lean.statement` is copied verbatim from `theorem` through the signature,
excluding `:= by`; every other node field is unchanged. The declaration docstring
contains the complete eight-step node proof and its cited dependencies.

## Second reading by N7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
