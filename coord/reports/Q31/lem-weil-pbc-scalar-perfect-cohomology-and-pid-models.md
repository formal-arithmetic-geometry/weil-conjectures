## Worker report

The module `Sheaf.CategoryTheory.DerivedCategory.ScalarPerfectCohomologyAndPidModels`
states `DerivedCategory.scalar_perfect_cohomology_and_pid_models`, with one `sorry` and
no new definitions. The node is unchanged except for `lean`. There is no statement dispute,
statement correction, new node, or dependency repair. No repair handoff was found for this item.

Hypothesis and clause correspondence:

- A commutative Noetherian ring is `(A : Type u) [CommRing A] [IsNoetherianRing A]`.
  The chosen module derived category is supplied by
  `[HasDerivedCategory.{w} (ModuleCat.{u} A)]`. The localization universe `w` is independent
  of `u`, exactly as in the recorded perfect-ring-complex interface.
- The first conjunct quantifies over every `P : DerivedCategory (ModuleCat.{u} A)` and
  assumes `IsPerfectRingComplex P`. For every integer `q`, it concludes
  `Module.FinitePresentation A ((homologyFunctor (ModuleCat.{u} A) q).obj P)`.
- The rest of that conjunct quantifies universally over a representative `C`, integer
  endpoints `a b`, the term bounds `C.IsStrictlyGE a` and `C.IsStrictlyLE b`, finite-projective
  terms `∀ i, Module.Projective A (C.X i) ∧ Module.Finite A (C.X i)`, and
  `Nonempty (P ≅ Q.obj C)`. For every `q < a ∨ b < q`, the corresponding cohomology
  object is `IsZero`. This is vanishing outside the term interval of every representative,
  rather than merely an unspecified cohomology bound.
- The second conjunct adds exactly the PID assumptions `[IsDomain A]` and
  `[IsPrincipalIdealRing A]`. The former includes nontriviality and no zero divisors;
  the latter says each ideal is principal. These assumptions apply only to the PID clause.
- A finitely presented module is `(N : ModuleCat.{u} A) [Module.FinitePresentation A N]`.
  The finite rank is `(r : ℕ)` and the *specified* map is
  `(v : (Fin r → A) →ₗ[A] N)`, with `Function.Surjective v`. Thus no replacement
  surjection, basis, freeness, or torsion-free assumption on N is supplied as a hypothesis.
- The witnesses `(s : ℕ)` and `(u : (Fin s → A) →ₗ[A] (Fin r → A))` satisfy
  `Function.Injective u` and `LinearMap.range u = LinearMap.ker v`.
- The augmented two-term model is witnessed by `F`, with `F.IsStrictlyGE (-1)` and
  `F.IsStrictlyLE 0`. Isomorphisms `em` and `e0` identify its two terms with the exact
  coordinate modules `A^s` and `A^r`. The equation
  `F.d (-1) 0 = em.hom ≫ ModuleCat.ofHom u ≫ e0.inv` identifies its differential with u.
  This specifies the complex `[A^s → A^r]` up to the standard term identifications,
  with zero terms elsewhere. Every term is consequently finite free.
- The augmentation `ε` has target the cochain complex
  `(CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N`. It satisfies `QuasiIso ε`.
  The degree-zero equation
  `ε.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).hom = e0.hom ≫ ModuleCat.ofHom v`
  retains the given v, and `∀ i, i ≠ 0 → ε.f i = 0` specifies its other components.
- The last two conjuncts say that the derived object
  `(singleFunctor (ModuleCat.{u} A) 0).obj N` is `IsPerfectRingComplex` and belongs to
  `(ObjectProperty.singleton ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))).triangEnvelope`.
  The nonempty singleton makes this exactly the thick closure from `pur9-def-thick`,
  including zero, isomorphism, shift, cone, and retract closure.

Dependency declarations read and reused:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`, `Q`;
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`: `homologyFunctor` and its
  factorization through Q. These implement `def-weil-abstract-derived-category`.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`, the recorded bounded finite-projective-model predicate.
- `Mathlib.Algebra.Module.FinitePresentation`: `Module.FinitePresentation`.
- `Mathlib.Algebra.Module.Projective`: `Module.Projective`.
- `Mathlib.LinearAlgebra.FreeModule.Basic`: `Module.Free`; finite coordinate modules have
  their usual finite coordinate bases, so the statement uses the actual coordinate modules.
- The `pur9-def-thick` Mathlib match: `CategoryTheory.ObjectProperty.IsTriangulated`
  (`Mathlib.CategoryTheory.Triangulated.Subcategory`), `IsStableUnderRetracts`
  (`Mathlib.CategoryTheory.ObjectProperty.Retract`), and `triangEnvelope`
  (`Mathlib.CategoryTheory.Triangulated.Generators`). Its nonempty singleton needs no zero seed.

The modules for all stated proof dependencies are imported, directly or through their recorded
statement dependencies. In particular the proof uses `Submodule.FG.of_le`
(`Mathlib.RingTheory.Noetherian.Basic`), `Module.finitePresentation_of_finite`
(`Mathlib.Algebra.Module.FinitePresentation`), `Submodule.nonempty_basis_of_pid`
(`Mathlib.LinearAlgebra.FreeModule.PID`), `Module.Projective.of_free`
(`Mathlib.Algebra.Module.Projective`), and
`DerivedCategory.isPerfectRingComplex_eq_triangEnvelope_singleton`
(`Sheaf.CategoryTheory.DerivedCategory.PerfectRingClassicalGenerator`). The six-step natural-language
proof of the DAG is recorded in the theorem docstring, with the dependency ids.

Edge cases checked before writing:

- The first conjunct permits the zero ring; the PID conjunct requires a domain, as the node says.
- Zero P and even a reversed interval a > b are allowed; then a model with those bounds is zero,
  and the stated vanishing applies in every degree.
- There is no requirement that r or s be positive. For r = 0, surjectivity forces N = 0 and
  the empty model works. For N = 0 and arbitrary r, take u to identify A^r with the full kernel;
  its two-term complex is acyclic. An isomorphism v permits s = 0.
- Over A = ℤ, the map ℤ → ℤ/2ℤ is allowed: take s = r = 1 and u multiplication by 2.
  This confirms that no torsion-free hypothesis has slipped into the quotient clause.
- Over a field the kernel may have any finite rank, including zero. No quotient is required to
  have the same rank as the middle module.
- The support is explicitly [-1,0], with u going from degree -1 to degree 0; N is in degree 0.
- The representative quantifiers are universal, not an existential choice of a favorable bound.

Sources opened: `literature/stacks-project/more-algebra.tex`, the complete definition-perfect,
lemma-perfect-module and lemma-perfect-ring-classical-generator passages (Tags 0657, 066Q, 0ATI).
These give the exact perfectness and thick-generation objects; Noetherian cycles and PID kernel
bases are the scalar supplement already spelled out in the node's proof. The existing
`StandardQuotientsPerfect` module was also read for its two-term augmentation convention, not
imported or copied: its private helper treats only a scalar multiplication presentation and
cannot state this arbitrary finite-rank specified-surjection assertion.

Searches made (2026-10-21):

- msearch LeanFinder: “Perfect complexes over a Noetherian ring have finitely presented cohomology
  and finite modules over principal ideal domains have augmented two term free resolutions”.
  Eight hits: projective-dimension predicates, K-projectivity and related resolution lemmas;
  no declaration states the combined node or its specified finite-rank augmentation.
- msearch Loogle: `"IsPerfect", "homology"` — zero hits.
- msearch grep of Mathlib:
  `(perfect|Perfect).*(FinitePresentation|homology)|homology.*(FinitePresentation|perfect)`
  — zero hits.
- msearch LeanSearch: “Cohomology of perfect complexes over Noetherian rings is finitely presented”.
  Eight hits, including `Module.finitePresentation_of_finite` and
  `Module.finitePresentation_iff_finite`; these supply an algebra ingredient only.
- rg of both `lean/WeilConjectures` and `lean/Sheaf` for perfect cohomology/homology and
  `twoTermResolution`: found a coherent-ring cohomology lemma, existing perfectness APIs,
  perfect-cohomology assembly, and the private scalar-resolution helper mentioned above.
  None states all clauses with the specified arbitrary finite-free surjection.
- rg of `lean/WeilConjectures` for the exact node id: no match.
- rg of Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for `scalar_perfect_cohomology_and_pid_models`: no preexisting declaration.

Validation: scompile.py compiled this file in both sandbox and library module contexts on the
server, cleanly (10.7 s and 12.4 s). All variables and universes are explicit; no file-local
notation, private definition, or local instance is introduced. The sole postponed proof is the
named theorem attached to this DAG node. The server preflight and delivery compile are run next.

## Second reading by Q31

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
