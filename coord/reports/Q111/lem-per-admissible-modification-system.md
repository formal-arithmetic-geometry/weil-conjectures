## Worker report

Item: lem-per-admissible-modification-system, Q111 stage 2.
Module: `Sheaf.AlgebraicGeometry.AdmissibleModificationSystem`.
Main declaration: `AlgebraicGeometry.AdmissibleModificationSystem.admissibleModificationSystem`.
Only the item's `lean` record changes. There are no new nodes, dependency repairs,
or statement corrections. The theorem has one `sorry`; no theorem is proved.
The six helpers have concrete bodies and are the vocabulary of this very system,
not independent replacement definitions of blowup, completion, or fibre product.

Source opened: ILO, Exposé XX §4.4, printed pp. 373–374 (PDF pages 379–380),
including Gabber's definition, the filtered-preorder and full-support identification
paragraph, and the final Note about the degreewise Rees map modulo I^m. Also read
its currently recorded six-step proof and the latest blueprint ancestor's Step 3.
The stage-1 repair note is resolved; the fresh split was reviewed on 2026-10-24.
No historical withdrawn theorem is rebound.

Hypothesis and clause correspondence:

- A commutative ring: `variable {A : Type u} [CommRing A]`, with explicit universe u.
  The theorem quantifies `I : Ideal A`, `[HenselianRing A I]`, and `hI : I.FG`.
  These are exactly the pair and finite-generation hypotheses, without a
  Noetherian, excellence, separatedness, or injective-completion hypothesis.
- A' and its canonical map: throughout, the actual `AdicCompletion I A` and
  `algebraMap A (AdicCompletion I A)`; I' is `I.map` along this map. The completion
  has the same universe u, so no class of rings is excluded.
- X and X': the existing `Spec (.of A)` and its counterpart for the completion.
  `puncturedOpen I` is the union of `PrimeSpectrum.basicOpen a` for a in I,
  exactly X minus V(I). The corresponding completed open is obtained by the
  same construction at I'; it is not replaced by an unrelated open scheme.
- The set of full-support ideals is `Index I`, the subtype of `Ideal A` cut out
  by `J.FG` and `PrimeSpectrum.zeroLocus (J : Set A) = ... I`. Thus support means
  the vanishing set of the ideal, not module-theoretic support of J.
- B_J is the recorded `AffineBlowup J.val`, with its recorded `toSpec` morphism.
  `closedFiber I J` is exactly `pullback (AffineBlowup.toSpec J) (Spec.map ...mk I)`.
- Domination is `Dominates J K`, existence of f : B_K → B_J with
  `f ≫ toSpec J = toSpec K`. The first conjunct is `Nonempty (Index I)`,
  `IsPreorder` for this relation, and `Directed ... id`. This is a filtered
  preorder, including the nonempty requirement and the correct direction.
- For each J, the second conjunct gives `j : U.toScheme ⟶ B_J`,
  `IsOpenImmersion j`, and `j ≫ toSpec J = U.ι`. For every open W of B_J,
  `Function.Injective (j.app W)` says exactly that the map of structure sheaves
  O_B → j_* O_U is injective on sections. It does not replace schematic density
  by topological density or assume U is dense in X.
- Extension of ideals is the equivalence `e : Index I ≃ Index I'`, required on
  every J to have `(e J).val = J.val.map` of the canonical completion map.
  `Dominates J K ↔ Dominates (e J) (e K)` makes this the source's isomorphism of
  preorders. In particular it is order-preserving and cofinal: each completed
  index has an inverse image, whose extension dominates it by reflexivity.
- All m ≥ 1 are `m : ℕ` with `1 ≤ m`; all n ≥ 0 are unrestricted `n : ℕ`.
  `powerQuotient I (J^n) m` is the actual module quotient
  J^n / (I^m • top of J^n), hence J^n / I^m J^n. This is not the ambient ring
  A / I^m J^n, nor J^n / (J^n ∩ I^m). Its completed counterpart uses
  `(J^n).map ι`, equal to `(J.map ι)^n` by `Ideal.map_pow`.
  The additive equivalences are required to send every class of x to the
  class of ι(x), with membership supplied by Mathlib's `Ideal.mem_map_of_mem`.
  Consequently they are the canonical module isomorphisms, including scalar
  compatibility, rather than arbitrary additive equivalences.
- Compatibility with Rees multiplication is expressed additionally by the
  ring equivalences of `reesQuotient I J m`, the existing Rees algebra modulo
  the extended coefficient ideal I^m. For every Rees polynomial F, its image
  is required to be the residue of the existing `reesGrading.hom ι rfl F`.
  This is coefficientwise ι, respects every homogeneous piece, and agrees
  with the preceding power maps. These representative identities fix all
  maps uniquely. Reduction from any larger exponent to a smaller positive
  one sends the same representative F to F on both sides, so the identities
  also impose compatibility in m; no independent arbitrary choices remain.
- The last conjunct specifies the residue-ring equivalence e₀ by
  e₀([a]) = [ι(a)] for every a. For every J it supplies an isomorphism from the
  completed closed fibre to `closedFiber I J`. Its first projection is the
  existing `AffineBlowup.hom ι rfl`, and its second projection is the map
  `Spec.map e₀.toRingHom`. Thus it is the canonical comparison of closed
  fibres over the canonical identification A/I ≅ A'/I', not an abstract
  nonempty isomorphism of unrelated schemes.

Dependency declarations inspected in source and used:

- `WeilConjectures.Mathlib.RingTheory.Henselian`: its documented identification
  of the henselian-pair terminology with Mathlib `HenselianRing A I`;
  `Mathlib.RingTheory.Henselian` contains the full class signature.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion` as compatible
  quotient sequences; `...Algebra`: its ring/algebra instances and canonical map.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `WeilConjectures.Blowup.Affine.Defs`: `AffineBlowup`, `AffineBlowup.toSpec`.
- `WeilConjectures.Blowup.AdmissibleBlowup`:
  `IsAdmissible.isIso_blowupMap_restrict`, the existing over-open interface.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; `Mathlib.AlgebraicGeometry.Pullbacks` supplies
  existence for schemes.
- Canonical comparison maps already exist in
  `WeilConjectures.Blowup.Affine.Functoriality`: `reesGrading.hom` and
  `AffineBlowup.hom`; their full definitions and structure-map identities were read.
- Proof-only imports: `Mathlib.RingTheory.Finiteness.Ideal`
  (`Ideal.exists_pow_le_of_le_radical_of_fg`),
  `Mathlib.RingTheory.AdicCompletion.Completeness`
  (`AdicCompletion.pow_smul_top_eq_ker_eval`), and
  `WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange`
  (`Scheme.GradedAlgebraData.PullbackData.relProjIsoPullback`). Principalization
  is already imported by the recorded admissible-blowup dependency. The genuine
  proof-only node lem-per-blowup-domination-ideal-factorization has no Lean
  declaration yet, so there is no module to import for it; it is not needed to
  type this theorem and is not restated as another sorry.

Edge cases checked mathematically before and while drafting:

- I = 0: completion is A, the full-support finitely generated ideals are
  nilpotent, their blowups and U are empty, and all displayed comparisons
  retain their meaning. No nonempty-spectrum hypothesis occurs.
- Nilpotent I and the zero ring: empty schemes, empty opens, zero quotients,
  and the filtered index set are allowed. I itself is always an index.
- J = A where permitted: the blowup is Spec A. A henselian pair has I in the
  Jacobson radical, so I = A is possible only in the zero ring; nothing in
  the encoding imposes a contradictory extra nontriviality hypothesis.
- n = 0: J^0 = A; the power quotient is A/I^m. n is not restricted to be
  positive. m = 1 gives the closed-fibre comparison, and no assertion for
  positive-m hypotheses is inferred from an excluded m = 0 case.
- Completion need not be flat and A → A' need not be injective. The proof
  docstring uses quotient comparisons and kernels, exactly as the DAG proof.
- Domination is a preorder rather than antisymmetric on ideals. The ideal
  equivalence is not an identification of distinct ideals with the same blowup.

Searches actually run for this delivery:

- msearch.py leanfinder, “The full support admissible blowups of a finitely
  generated ideal form a filtered preorder and extension to adic completion
  identifies the preorder and closed fibres”: AdicCompletion, IsAdicComplete,
  flat_of_isNoetherian, IsAdic, Hausdorffification, submodule,
  localCohomology.ideal_powers_initial, Ideal.Filtration. No exact statement.
- msearch.py loogle, “AdicCompletion, Ideal.map, AlgebraicGeometry.AffineBlowup”:
  zero hits; the service does not know the project's AffineBlowup identifier.
- msearch.py leansearch, “Adic completion induces an isomorphism of the preorder
  of full support admissible blowups and their closed fibres”: completion,
  its module/ring structure, of_bijective, congr, ofAlgEquiv, ofAlgEquiv_apply,
  Padic.adicCompletionEquiv. No exact statement.
- msearch.py grep, “admissible|blowup|reesAlgebra” in AlgebraicGeometry:
  five elliptic-curve variable-change hits, no blowup comparison theorem.
- rg over the named project Lean source trees for admissible, full-support,
  filtered preorder, completion/blowup, Rees, and the item id: existing
  AffineBlowup and its functoriality found and reused, but no existing system
  statement. `dag/lean_names_upstream.json` has no entry for this item.
- The existing `SchematicallyDenseOpen` vocabulary was found and read in
  `Sheaf.TraceFormula.SchematicallyDenseOpen`. Here schematic density is
  written directly as injectivity of j.app on every open, as in the item's
  parenthetical definition; no second named definition of density is made.

Validation: scompile.py compiled the delivered module on the server in both
sandbox and library module modes, cleanly (12.6 s and 3.5 s). All universes and
variables are bound explicitly; no diagnostic commands remain. The file is
within 100 columns. All final compilation and delivery validation use the
prescribed wrappers. Process note: two initial type probes were mistakenly
run locally from /tmp before switching to the required sandbox/server workflow;
these were not delivery files and no live source was edited.

## Second reading by Q111

A second in-thread reading was made with the current node and final Lean source
open. The dispatcher explicitly forbids launching another agent; this section
records that self-audit, and does not claim independent review. The maintainer's
independent reading is still required by the brief.

Checked each of the correspondences above against the final theorem. The first
compile's explicit coercion and noncomputability faults were fixed: vanishing
loci take `(J : Set A)`; the open construction is noncomputable; the degreewise
representative binder is `x : ↥(J.val ^ n)`. The clean recompile confirms that
the closed-fibre projection identities elaborate with the actual pullbacks.
Read all six helper bodies: each is a subtype, existential relation, union of
existing basic opens, existing pullback, or an actual standard quotient.
No data is chosen from an unspecified existence theorem. The canonical
representative identities and both closed-fibre projections rule out arbitrary
comparison maps. No hypothesis, clause, positivity case, or ring universe was
lost. No statement dispute or mathematical correction was found.
