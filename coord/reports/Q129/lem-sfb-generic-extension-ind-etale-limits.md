## Worker report

The module `Sheaf.AlgebraicGeometry.GenericExtensionIndEtaleLimits` states all clauses of
`lem-sfb-generic-extension-ind-etale-limits` in three named theorems, each with proof `sorry`.
It introduces no definitions, new nodes, dependency repairs, or statement corrections.
The only change to the item's JSON is its `lean` field.

Hypothesis and conclusion correspondence:

- A commutative ring A, a commutative ring B and the specified base change A to B are
  `(A B : Type u) [CommRing A] [CommRing B] (f : A →+* B)` in
  `AlgebraicGeometry.genericExtension_bijective_of_indEtale`.
- The ind-etale hypothesis is `hf : f.IndEtaleAcrossUniverses`, the recorded dependency
  predicate. It is canonical ULift transport of the upstream ind-etale predicate, whose
  data is a small filtered presentation by etale A-algebras. Those etale algebras are
  finitely presented, as stated in `Algebra.IndEtale.etale_le_finitePresentation`.
- The element to invert is `(t : A)`. `Localization.Away t` inverts the submonoid
  `Submonoid.powers t`, including power zero; no nonzero, nonunit, regular, or
  nonnilpotent condition is imposed.
- N over Spec A is `(N : Over (Spec (CommRingCat.of A)))`; `[Smooth N.hom]`
  is exactly its smooth structure morphism. Its separatedness is written in the
  node's explicit form `[IsClosedImmersion (pullback.diagonal N.hom)]`.
  There is no quasi-compactness, finite-type, or group-scheme hypothesis on N.
- The full initial mapping property is `hN : ∀ X : Over (Spec (.of A)),
  Smooth X.hom → Function.Bijective ...`. Its source is `X ⟶ N`, precisely
  Hom_A(X,N). Its function is the map of `Over.pullback` along
  `Spec.map (.ofHom (algebraMap A (Localization.Away t)))`. By the definition of
  `Over.pullback`, the function has codomain the relative Hom set between the
  pullbacks X[1/t] and N[1/t], over Spec A[1/t]. This specifies the canonical
  restriction, including its action on maps, rather than an arbitrary bijection.
- The conclusion quantifies over every `Y : Over (Spec (.of B))` with `Smooth Y.hom`.
  The target over B is `(Over.pullback (Spec.map (.ofHom f))).obj N`, whose
  underlying scheme is `pullback N.hom (Spec.map (.ofHom f))` and whose structure
  map is `pullback.snd`. Thus it is exactly N_B. The restriction functor is
  pullback along `algebraMap B (Localization.Away (f t))`, so its target is the
  stated Hom over B[1/t]. No affineness, separation, or quasi-compactness of Y
  is imposed.
- The final strict-henselization clauses are
  `AlgebraicGeometry.genericExtension_strictHenselization_tensorSquare` and
  `AlgebraicGeometry.genericExtension_strictHenselization_tensorFactor`.
  They bind a local commutative R, a residue separable closure K with its compatible
  R-algebra structure, and a commutative R-algebra D with the recorded
  `Algebra.StrictHenselizationPresentationIn.{u,v} R K D`. All auxiliary data is
  precisely the data in that dependency's definition of a strict henselization.
  R lives in Type u, while K and D may live in Type (max u v); the diagrams are
  therefore never made vacuous by placing test algebras below the base universe.
- In the binary clause `f : D →ₐ[R] D ⊗[R] D` and
  `hf : f = Algebra.TensorProduct.includeLeft ∨ f = Algebra.TensorProduct.includeRight`
  range over exactly the two specified maps, respectively d ↦ d ⊗ 1 and d ↦ 1 ⊗ d.
  The conclusion includes their ind-etaleness and the full restriction bijection
  for the base-changed N. The assumptions on N and t are exactly the original ones
  with A replaced by D.
- In the finite-power clause `(n : ℕ) (k : Fin n)` specifies every factor of
  `⨂[R] _ : Fin n, D`, the n-fold tensor power. The actual map is Mathlib's
  `PiTensorProduct.singleAlgHom (R := R) (A := fun _ : Fin n ↦ D) k`,
  sending d to the pure tensor with d in position k and 1 elsewhere. The conclusion
  includes its ind-etaleness and restriction bijectivity for all smooth schemes
  over this tensor power, localized at this factor map's image of t. This is the
  node's clause with source A = D, not a DVR-only assertion about the tensor ring.

Recorded statement dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and its morphisms; full structure signature and docstring read.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth`; full affine-local signature and docstring read.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`; definitions and docstrings read.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`; full signature and docstring read.
- `def-pc-base-change`: `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`
  imported publicly. Its documentation specifies that scheme base change is
  `Over.pullback` / `Limits.pullback`, not the record's module-sheaf functor.
  `CategoryTheory.Over.pullback` in Mathlib's `CategoryTheory.Comma.Over.Pullback`
  was read in full, including its object and map definitions; it is used directly.
- `def-weil-pbc-ind-etale-algebra`:
  `Sheaf.RingTheory.IndEtaleUniverseTransport`, `RingHom.IndEtaleAcrossUniverses`.
  Its complete signature, definition, and docstring, and the upstream
  `Algebra.IndEtale` filtered presentation were read.
- `def-sc-ring-strict-henselization`:
  `Sheaf.RingTheory.StrictHenselizationPresentationIn`,
  `Algebra.StrictHenselizationPresentationIn`. The pointed diagram, cocone,
  isColimit and specified identification fields were read in full, together with
  the original presentation module it imports.

The modules of all recorded proof dependencies with Lean declarations were imported
plainly, including the affine-limit criterion, smooth-algebra descent, etale/smooth
comparison, directed reindexing, pointed-etale filteredness and ind-etale stability.
Mathlib proof dependencies for smooth base change/composition and open restriction
are already supplied by the public Smooth import; Spec limits and gluing by the
plain GammaSpecAdjunction and Gluing imports. The theorem docstrings carry the
seven-step proof plan, separated into the general six steps and the tensor clause.

Source checks: read the local Stacks sources at limits.tex, proposition
`proposition-characterize-locally-finite-presentation`, and algebra.tex,
`lemma-smooth-descends-through-colimit`; verified these against the primary pages
https://stacks.math.columbia.edu/tag/01ZC and https://stacks.math.columbia.edu/tag/0CAQ.
Read the current blueprint's direct-images proof under `literature/blueprint/latest/`.
The item is the explicitly agent-written principal-open extension of the BLR argument;
no BLR-only hypothesis was substituted for that agent statement.

Edge cases checked before writing: t a unit (localization is the identity up to
canonical isomorphism); t = 0 or nilpotent (empty localized base, so the hypothesis
itself is restrictive, but never dropped); zero B; empty test schemes; non-qc N;
non-qc and non-separated Y; n = 1 (canonical one-factor identification); n = 0
(no specified factor, expressed by Fin 0); and unequal base/strict-henselization
universes. No field, domain, DVR, or nonemptiness assumption is inserted.
No statement dispute or correction was found.

Searches for an existing statement:

- `msearch.py ... leanfinder "Unique extension of morphisms from smooth schemes
  across a principal open is preserved by ind etale base change"`: eight results,
  all general etale/smooth base-change or chart results, including
  `AlgebraicGeometry.IsEtale.instIsStableUnderBaseChangeScheme` and
  `AlgebraicGeometry.IsSmooth.exists_isStandardSmooth`; none is this mapping property.
- `msearch.py ... leansearch "Neron mapping property preserved by ind etale base
  change"`: eight general etale/smooth/tensor stability results; no extension theorem.
- `msearch.py ... loogle "RingHom.IndEtale, Function.Bijective"`: no hits;
  the index reports unknown identifier RingHom.IndEtale, so this query alone
  establishes no absence. Retried with `"Function.Bijective", "pullback"`:
  successful search, zero hits.
- `msearch.py ... grep "Neron|neron|genericExtension|generic_extension"
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` over both `lean/WeilConjectures/AlgebraicGeometry` and
  `lean/Sheaf/AlgebraicGeometry` for extension-property names found only
  `exists_stable_pointed_generic_extension`, which is stable-curve extension,
  not restriction of maps into smooth separated schemes. The requested grep
  for the item's id in `lean/WeilConjectures` returned no hits.
- Searched all Mathlib, WeilConjectures, Sheaf, and `dag/lean_names_upstream.json`
  for all three proposed theorem names: zero collisions. No repair note names
  this item. Searched Mathlib tensor-power/PiTensorProduct sources and used its
  existing commutative-ring tensor product and `singleAlgHom`, with no copy.

Validation: prescribed `scompile.py` compiled the entire module in both its sandbox
and library modes cleanly (2.7 s and 2.6 s for the final source). There are exactly
three named sorry proofs and no helper definitions or diagnostic commands.

## Second reading by Q129

I reopened the item and read each of the three final theorem signatures in a fresh
pass. This is the assigned worker's second reading; no separate worker was started,
as the dispatcher explicitly prohibits starting other agents. The maintainer's
independent delivery review remains required.

The general signature retains A, t, smoothness, the closed diagonal, the universal
initial restriction bijection, the specified ind-etale map and the universal final
restriction bijection. The pullback objects and map types identify both Hom sets
with the node's relative Hom sets, not with unrestricted scheme maps. The target
localization is at f(t), not a newly chosen B-element. No qc condition occurs.
The binary signature includes both canonical maps via its exact disjunction, and
its source ring remains D. The finite signature includes every n and every factor k;
its target localization is at `singleAlgHom k t`, with all other factors set to 1.
The strict-henselization witness is the recorded presentation in the correct common
algebra universe. All conclusions retain both ind-etaleness and the desired mapping
property. No mismatch was found and no statement change was made.
