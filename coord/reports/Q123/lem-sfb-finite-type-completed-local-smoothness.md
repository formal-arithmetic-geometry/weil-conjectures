## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteTypeCompletedLocalSmoothness` states
`AlgebraicGeometry.smooth_on_open_iff_formallySmoothAdic_completion`, with one
postponed proof and no new definitions. Only the item's `lean` record changes.
No statement correction, new nodes, or dependency interface repairs are needed.
The node has no repair note. The prescribed CompactObject example module is now
withdrawn; the current module-mode conventions in brief-stage2 section 4 were followed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Commutative Noetherian local base `(R,m_R)`: `{R : Type u}`, `[CommRing R]`,
  `[IsNoetherianRing R]`, `[IsLocalRing R]`, and `IsLocalRing.maximalIdeal R`.
- Finite type commutative R-algebra B: `{B : Type u}`, `[CommRing B]`,
  `[Algebra R B]`, `[Algebra.FiniteType R B]`. The latter means the top
  subalgebra is finitely generated, exactly the node's algebra-generation condition;
  no module-finiteness or finite-presentation hypothesis is imposed.
- Prime q: `(q : Ideal B) [q.IsPrime]`.
- Its inverse image is the base maximal ideal:
  `hq : Ideal.comap (algebraMap R B) q = IsLocalRing.maximalIdeal R`.
- T = B_q: `Localization.AtPrime q`, with its canonical B- and R-algebra
  structures and its existing local-ring instance.
- qT: `IsLocalRing.maximalIdeal (Localization.AtPrime q)`. The recorded
  localization API `IsLocalization.AtPrime.map_eq_maximalIdeal` identifies
  this ideal with the extension of q.
- C = the inverse limit of T/(qT)^n:
  `AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
    (Localization.AtPrime q)`. Mathlib's compatible-sequence construction
  includes the n=0 coordinate, which is the zero quotient and imposes no
  additional condition. The canonical R-algebra structure is induced through T.
- Smoothness on an open neighbourhood of q:
  `∃ W : (Spec (CommRingCat.of B)).Opens,
    (⟨q, inferInstance⟩ : PrimeSpectrum B) ∈ W ∧
    Smooth (W.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)))`.
  Here W is the open subscheme and its structural morphism is the inclusion
  followed by the given affine structural morphism.
- If and only if: the conclusion uses `↔`, with both directions present.
- Formal smoothness of R -> C for m_C: `Algebra.FormallySmoothAdic R C`
  at the explicitly written ideal
  `(IsLocalRing.maximalIdeal (Localization.AtPrime q)).map
    (algebraMap (Localization.AtPrime q) C)`.
  This is m_C by `AdicCompletion.maximalIdeal_eq_map`, since finite type over
  Noetherian and then localization make T Noetherian. This spelling avoids
  requiring a separate Noetherian/local instance witness in the signature,
  and does not assume an additional hypothesis. It is the ideal of the node,
  not the extension of m_R and not a different completion topology.

Both rings live in one arbitrary universe `u`, as required by Mathlib's scheme
category; any pair of small rings can be placed in a common universe. The
existing adic predicate tests rings in the same universe as the base and C,
following its recorded `max u v` convention. No independent smaller test
universe, residue-field size condition, characteristic restriction, or
separability condition is imposed. All variables and the universe are explicit.

Statement dependencies used (the actual source signatures and docstrings were read):

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`,
  its canonical algebra and local-ring structures, and
  `IsLocalization.AtPrime.map_eq_maximalIdeal`.
- `Mathlib.RingTheory.AdicCompletion.Basic` (publicly through Algebra):
  `AdicCompletion`; `Mathlib.RingTheory.AdicCompletion.Algebra`: the ring
  and induced algebra structures.
- `Mathlib.AlgebraicGeometry.Scheme` (publicly through Smooth):
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `WeilConjectures.RingTheory.FormallySmoothAdic`:
  `Algebra.FormallySmoothAdic`, the continuous square-zero lifting predicate.
- `Mathlib.RingTheory.FiniteType`: `Algebra.FiniteType` supplies the finite
  generation notion already present in the node, not a new definition.

Every recorded proof dependency module is imported without `public` unless
already a public statement import. These include localization Noetherianity,
completion locality, the basic-open basis, open immersions and smooth restriction,
the affine ring-map comparison, smooth/localization square-zero lifting,
`Algebra.FormallySmoothAdic.adicCompletion` in
`WeilConjectures.RingTheory.FormallySmoothAdicCompletion`, and
`AlgebraicGeometry.smooth_on_open_iff_artinian_lifting` in
`WeilConjectures.AlgebraicGeometry.SmoothAtPrimeArtinianLifting`, together with
Artinian nilpotence and the completion quotient projection results. The six
steps of the accepted node proof are reproduced in the theorem docstring,
including the explicit principal-open affine comparison in step 2.

Source verification: read `literature/stacks-project/more-algebra.tex`,
lemma-formally-smooth-finite-type (Tag 07VH), including its proof, and
lemma-formally-smooth-completion (Tag 07ED), including its proof. Specializing
07VH to a local base at its maximal ideal, and 07ED to completion of B_q,
gives exactly this node. The base is not assumed complete.

Edge cases checked mathematically before writing:

- Identity algebra B=R, q=m_R: the open neighbourhood exists and the adic
  completion is adically formally smooth by localization/identity lifting and
  completion; completeness of R is unnecessary.
- R=k and B=k[x], q=(0): q need not be maximal in B. Its localization and
  completion are k(x), with zero maximal ideal, so the adic predicate becomes
  ordinary lifting. This case remains included, including transcendental residue fields.
- R=k and B=k[e]/(e^2), q=(e): smoothness fails, and the completion equals B.
  The square-zero quotient k[e]/(e^3) -> k[e]/(e^2) has no algebra section
  (a lift of e has nonzero square); its identity test is continuous. Thus the
  right side also fails, so the predicate is not tautological.
- R=k, B=k[x], q=(x): C=k[[x]], with its x-adic ideal, rather than ordinary
  discrete formal smoothness or completion at the zero base ideal.
- The zero ring B has no prime q and the zero ring R is not local under the
  supplied nontrivial local-ring convention; there is no excluded valid point.
  The membership q in W prevents using the empty open as a witness.
- Arbitrary characteristic and zero generators are allowed.

Searches for an existing statement:

- `msearch.py ... leanfinder` with query "For a finite type algebra over a
  Noetherian local ring, smoothness on a neighbourhood of a prime over the
  maximal ideal is equivalent to maximal ideal adic formal smoothness of its
  completed local ring": eight hits, including `Algebra.IsSmoothAt`,
  `Algebra.smoothLocus`, and `Algebra.IsSmoothAt.exists_notMem_smooth`;
  none gives the completed local adic equivalence.
- `msearch.py ... leansearch` with query "A finite type algebra over a
  Noetherian local ring is smooth near a prime if and only if its completed
  local ring is formally smooth for the maximal ideal adic topology": eight
  hits for discrete formal smoothness, smoothness and localization; no match.
- `msearch.py ... loogle 'AdicCompletion, Algebra.FormallySmooth'`: two hits,
  `Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq` and
  `Algebra.FormallySmooth.exists_kerProj_comp_eq_id`; these lift maps into
  completions, not detect a smooth open neighbourhood from a completed local ring.
- `msearch.py ... grep
  'FormallySmooth.*[Aa]dic|[Aa]dic.*FormallySmooth|formallySmooth.*[Cc]ompletion'
  RingTheory`: one hit, a doc reference in Smooth/AdicCompletion.lean; no match.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for
  `completed_local|completedLocal|smooth.*adic|FormallySmoothAdic` found the
  recorded adic predicate, completion lifting and descent APIs, and unrelated
  completed local rings, but no smooth-open/completed-local equivalence.
  The more specific `smooth_on_open_iff.*complet|completed_local_formally|finite_type_completed`
  search found no declaration. Searching the exact blueprint id upstream
  found no match. The proposed declaration name also has no hit in
  `dag/lean_names_upstream.json`, Mathlib, upstream, or Sheaf.

Validation: the prescribed `scompile.py Q123
lem-sfb-finite-type-completed-local-smoothness <module>` compiled both its
sandbox and library-name checks successfully with no diagnostics. The module
contains no proofs besides the required `sorry`. No STATEMENT-DISPUTED fault.

## Second reading by Q123

Sequential second pass by this worker; the dispatcher explicitly prohibits
starting another agent. Independent maintainer review remains required.

Reopened the node and the completed module, and checked the quantifiers and
conclusion against the source: R is local and Noetherian, B is only finite
type, q is prime and lies over m_R, the left side is an actual open smooth
neighbourhood in Spec B, and the right side is the canonical completion of B_q
with the extended ideal equal to m_C. The base map is the same algebraMap in
both sides. There is no arbitrary replacement ring or replacement morphism,
no new test-algebra restriction, and no extra completeness or separability
assumption. In particular, q is not silently required maximal, and m_R C
has not been substituted for m_C. All six proof steps and all available proof
dependency imports were checked. No mismatch was found and no statement change
was made. The only node-field delta is the Lean binding.
