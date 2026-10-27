## Worker report

Repair of returned immutable head 8f11cc56c942, stage 2, group NW,
lem-sfb-proj-graded-sheafification-exact, 2026-10-22 UTC.

The sandbox supplied to this retry contained only dispatcher marker files, with no
retained Lean, node, or report. I read the current live node, the dependency records,
and their source declarations. The item node is copied from the current shared
repository and differs ONLY in `lean`. In particular its statement, stmt_deps,
proof, proof_deps, proof_origin, mathlib_searches, split_report and reviewed fields
are preserved. This supersedes the stage-1 re-split described in the return entry.
No stage-1 split is being delivered again.

The new module `Sheaf.AlgebraicGeometry.ProjGradedSheafificationExact` contains one
statement, `AlgebraicGeometry.Proj.graded_sheafification_shortExact`, whose proof is
`sorry`. There are no definitions, extra axioms, private notions, or extra nodes.
The source is Stacks Project constructions.tex, Tag 01M7, lemma-proj-sheaves,
final assertion; I read the definition preceding it and the lemma and proof.

Clause-by-clause statement correspondence:

- A nonnegatively graded commutative ring S is `{S : Type u} [CommRing S]`,
  `𝒜 : ℕ → AddSubgroup S`, `[GradedRing 𝒜]`. This is an internal direct-sum ring
  grading, with multiplication and unit compatibility, not a field or polynomial
  specialization. The scheme X is literally `AlgebraicGeometry.Proj 𝒜`.
- The three S-modules are `M : Fin 3 → Type u`, with
  `[∀ j, AddCommGroup (M j)]` and `[∀ j, Module S (M j)]`.
  The integer-indexed subgroups `𝓜 : ∀ j, ℤ → AddSubgroup (M j)` and
  `h𝓜 : ∀ j, DirectSum.IsInternal (𝓜 j)` render the full ℤ-grading, including
  arbitrary negative degrees. The scalar rule S_a(M_j)_b ⊆ (M_j)_(a+b) is
  `hsmul`, for every j, natural n, integer z, scalar a and element y.
- The associated sheaves in clause (1) of def-weil-pbc-proj-twisting-sheaf are
  `F : Fin 3 → (Proj 𝒜).Modules`, equipped with the chart identifications of
  `gradedModuleSheaf_exists`. They are written in the same interface used by
  the recorded `tilde_functorial`: `alpha` is the additive map into ordinary
  localization, and `halpha` says it is injective and its range is exactly
  `LocalizedModule.degreeZeroFractions`. Thus it is precisely an additive
  equivalence with M_(f), not a bare arbitrary sheaf or a Nonempty choice.
  `hscalar` is compatibility with S_(f) acting through `awayToSection`.
  `hres` is the canonical restriction formula for D₊(g) ⊆ D₊(f), using a
  homogeneous relation g^e = a*f: y/f^m maps to a^m*y/g^(e*m).
  These are the defining chart, scalar and restriction identifications of the
  associated sheaf, supplied by the already recorded existence theorem; they
  are not additional restrictions on S or M. The source's `Proj.twist` concerns
  S(d), so it cannot be substituted for the general M here.
- The maps u and v are `phi : M 0 →ₗ[S] M 1` and
  `psi : M 1 →ₗ[S] M 2`. Their degree preservation is `hphi` and `hpsi`,
  universally quantified over integer z and elements of the corresponding
  homogeneous piece.
- Exactness of 0 → M_0 → M_1 → M_2 → 0 is the three hypotheses
  `hinj : Function.Injective phi`, `hexact : Function.Exact phi psi`, and
  `hsurj : Function.Surjective psi`. No splitting is assumed, and zero
  composite of the linear maps follows from middle exactness.
- The induced maps are `i : F 0 ⟶ F 1` and `q : F 1 ⟶ F 2`, with `hi` and
  `hq` precisely the chart fraction formulas of `tilde_functorial`:
  alpha(s) = y/f^m implies alpha(i(s)) = phi(y)/f^m, and likewise for q.
  The dependency's uniqueness clause identifies these maps with its lift;
  no arbitrary sheaf morphism is substituted for the canonical one.
  Maps are characterized rather than selected, as in the already published
  projective-line specialization `Proj.proj_sheafification_shortExact`.
- The conclusion is
  `∃ h : i ≫ q = 0, (ShortComplex.mk i q h).ShortExact`.
  The witness asserts zero composite rather than assuming it. Mathlib's
  ShortExact comprises exactness, monicity of i, and epicity of q, giving
  exactly the claimed short exact sequence of O_X-modules.
- There is no degree-one generation, Noetherian, finite generation, field,
  nonempty Proj, or nonzero localization hypothesis. The common ambient
  universe u is explicit, as in both recorded associated-sheaf interfaces;
  it is arbitrary, with no fixed size bound. There are no auto-bound variables,
  local notations, local instances, hidden lets, or `show ... from` terms.

Dependency declarations read and used:

- def-pc-proj is a Mathlib leaf, with its recorded matches
  `AlgebraicGeometry.Proj`, `AlgebraicGeometry.projIsoSpec` in
  Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme and
  `ProjectiveSpectrum.basicOpen` in ...Topology. Proj is the scheme of
  homogeneous primes away from the irrelevant ideal; projIsoSpec identifies
  positive-degree charts with Spec S_(f).
- def-weil-pbc-proj-twisting-sheaf records
  WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules,
  `AlgebraicGeometry.Proj.twist`. Its record explicitly directs general M
  consumers to `AlgebraicGeometry.Proj.gradedModuleSheaf_exists` in
  WeilConjectures.AlgebraicGeometry.ProjGradedModuleSheafExists. I read both
  full declarations and docstrings and use that existing chart interface.
  Twist.Modules is publicly imported as the statement-dependency record asks.
- lem-sc-p1-proj-tilde-functorial records
  WeilConjectures.AlgebraicGeometry.ProjTildeFunctorial,
  `AlgebraicGeometry.Proj.tilde_functorial`. Its full statement specifies the
  same alpha/halpha/hscalar/hres data and characterizes the induced arrows
  uniquely by exactly the fraction formulas used in hi/hq. The further mu/hgerm
  data supplies the stalk formula; our basis proof does not need a choice of
  stalk identifications. This module is publicly imported.
- The proof plan imports
  WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties
  (`AlgebraicGeometry.Proj.standardOpenProperties`),
  Sheaf.Algebra.Module.GradedLocalizationExact
  (`LocalizedModule.graded_localization_exact`), and
  WeilConjectures.AlgebraicGeometry.Modules.BasisExactness
  (`AlgebraicGeometry.Scheme.Modules.exactness_of_basis_sections`), all as plain
  proof imports. Each is the current recorded dependency interface.
- Mathlib.Algebra.Homology.ShortComplex.ShortExact supplies
  `CategoryTheory.ShortComplex.ShortExact`; the full definition is exactness
  plus monicity and epicity. It is publicly imported.

Edge cases checked before writing:

- S = 0, S concentrated in degree zero, or nilpotent positive-degree part:
  Proj can be empty. No nonempty hypothesis or point choice is required; the
  statement then concerns the zero sheaf category.
- f = 0 and any positive-degree nilpotent f are allowed as standard opens;
  the chart and localized module are zero. Their unique maps are short exact
  whenever the original sequence is. No non-zero-divisor condition occurs.
- M_0 = 0 or M_2 = 0 and all modules zero are admitted. Injectivity, exactness,
  surjectivity are the correct endpoint conditions in each case.
- Negative module degrees are retained. There is no truncation or degree-one
  assumption: for example a graded ring generated by a degree-two element is
  included. Restriction denominators have arbitrary positive homogeneous degree.
- A sequence need not split; the sheaf conclusion is categorical short
  exactness, not surjectivity on sections of every open. A non-Noetherian ring
  with an infinitely generated graded module is also admitted.

Searches for an existing exact statement (2026-10-22):

- msearch.py leanfinder: "The associated sheaf on Proj of a short exact sequence
  of integer graded modules over a nonnegatively graded ring is short exact".
  Eight hits: MayerVietorisSquare.shortComplex_shortExact / shortComplex_exact,
  Profinite.NobelingProof.succ_exact, IsLocalizedModule.map_exact,
  ModuleCat.localizedModule_functor_map_exact, SheafOfModules.instAbelian and
  projective resolution exactness. No exact match for associated sheaves on Proj.
- msearch.py leansearch: "associated graded module sheaf on Proj preserves short
  exact sequences". Eight hits on the Proj structure sheaf, awayToSection,
  and ordinary module presheaf sheafification preserving finite limits. No match.
- msearch.py loogle: "ShortComplex.ShortExact, Proj" reported unknown identifier
  ShortComplex.ShortExact. Repeated with fully qualified
  "CategoryTheory.ShortComplex.ShortExact": twelve hits giving ShortExact
  and its elementary properties, no Proj exactness theorem.
- msearch.py grep:
  `(graded|[Pp]roj|tilde).*(shortExact|[Ss]hortExact|sheafification_exact)` in
  AlgebraicGeometry/ProjectiveSpectrum: zero hits.
- rg in lean/WeilConjectures and lean/Sheaf for ProjSheafificationExact,
  sheafification_exact, tilde exactness and graded ShortExact found affine
  tilde material and the proper dependency interfaces, not this statement.
  The explicit node-id grep in lean/WeilConjectures found no match; the node
  occurs in the proof docstring of PlaneHypersurfaceCohomology in lean/Sheaf.
  The new declaration name was also checked against dag/lean_names_upstream.json
  and both source trees, with no hit.
- scompile.py --source Sheaf.AlgebraicGeometry.ProjSheafificationExact returned
  a withdrawn module with no declarations. The source of
  WeilConjectures.AlgebraicGeometry.ProjSheafificationExact states only the
  field/polynomial/Fin-2 projective-line specialization; it does not cover the
  present arbitrary graded commutative ring. Its chart-based interface was
  read for compatibility, but its special hypotheses are not imported here.

No statement correction, dependency repair, new node, or STATEMENT-DISPUTED
flag is needed. The module docstring and theorem docstring carry the item id
and Stacks source; the theorem docstring transcribes all three live proof steps,
including extension of the grading to ℤ and the three exact triples.

Validation: scompile.py compiled this exact module both as a sandbox probe and
at its library module name, cleanly (7.1 s and 6.7 s). All binders and universe
variables are explicit. The node's lean.statement is extracted verbatim from
the theorem keyword through its signature, before `:=`. JSON uses indent 1,
Unicode and a final newline. A field comparison with the shared node reports
only `lean`; no Lean line exceeds 100 characters.

## Second reading by NW

I reread the current node and the completed Lean file in a separate second pass.
This is a self-review, not a claimed second agent review: the dispatch brief
explicitly prohibits starting other agents, and the maintainer independently
reviews the delivery.

- H1 repaired: there is now one delivered module, one corresponding complete
  lean record, this Worker report and this Second reading section.
- H2 repaired: the node was recopied from current live source and only lean
  added. The returned proof/proof_origin/mathlib_searches/split_report rewrites
  are absent; the reviewed stage-1 split is preserved verbatim as JSON data.
- H11 repaired by checking the actual signature clause by clause: CommRing S
  with a natural-number GradedRing, Fin 3 modules with integer internal
  gradings, hsmul, degree-preserving phi and psi, all three underlying exactness
  conditions, and short exactness of the associated F 0 → F 1 → F 2 maps.
  There is no field/Noetherian/degree-one binder.
- The nontrivial interface point is that the recorded Proj.twist is for S(d),
  not general M. Its node's own note points to gradedModuleSheaf_exists for
  clause (1). I checked that declaration and retained its full chart scalar
  and restriction descriptions in hscalar/hres; these certify associated
  sheaves and do not add an algebraic hypothesis. No arbitrary Nonempty
  sheaf choice occurs.
- I compared hi/hq with the first uniqueness clause of tilde_functorial, not
  just its name: the numerator and exponent, the same denominator powers,
  chart open and source/target indices agree. Hence these are the induced
  maps, without assuming their composite vanishes.
- The conclusion produces h and then ShortExact. I opened the latter
  structure: it includes all three requirements, not merely middle exactness.
  This avoids silently dropping the two zeros from the exact sequence.
- The empty Proj/nilpotent-chart/zero-module and negative-grading cases remain
  expressible in the signature. There is no splitness or universal section
  surjectivity claim. No further mathematical mismatch was found.
