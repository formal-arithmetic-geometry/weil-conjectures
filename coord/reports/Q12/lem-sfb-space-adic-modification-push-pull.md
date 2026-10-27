## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceAdicModificationPushPull` states
`AlgebraicGeometry.AlgebraicSpace.exists_adicModification_pushPull`, with `sorry`
as its whole proof. The statement is Stacks 08BD with the comparison equation
in its proof and componentwise boundedness as defined in 08BA. Read the source
at spaces-more-morphisms.tex lines 9941–9987 and 9774–9798.
There is no statement correction, new node, new definition, or dependency repair.

Hypothesis and clause correspondence:

- Base scheme and universes: `{S : Scheme.{u}}`, `{V X : AlgebraicSpace S}`.
  Modules and section rings retain the shared algebraic-space universe `u`;
  their etale site has objects in `u+1`. There is no added universe equality.
- Both spaces are Noetherian: `hlnV`, `hlnX` quantify the recorded scheme
  `IsLocallyNoetherian` predicate over every etale chart; `hqcV`, `hqcX`
  are compactness of their point topologies; `hqsV`, `hqsX` are the existing
  absolute quasi-separatedness predicate (quasi-compact diagonal on affine tests).
  No separation or Noetherian hypothesis on the base scheme is imposed.
- Representable proper morphism: `q : V ⟶ X`, `hqrep : IsRepresentable q.hom.hom`,
  and `hqproper : MapIsProper q`, using the dependency's actual definitions.
- Quasi-coherent ideals: `J K : QuasiCoherentIdeal X`.
- Isomorphism above `U = X \ V(K)`: `hU` says that for every etale scheme chart
  `T` whose section ideal `idealSectionImage K.val.arrow T` is `⊤`, the actual
  presheaf fibre-product projection `pullback.snd q.hom.hom T.obj.hom` is an
  isomorphism. This is the chartwise expression of the given hypothesis, not
  a stronger global condition: a chart lies in U exactly when its ideal subsheaf
  is the unit ideal. A monic ideal inclusion has unit ideal of sections exactly
  in that case. Such charts cover U; isomorphisms descend on an etale covering.
  The presheaf pullback is representable by `hqrep`, so this is also the usual
  isomorphism of spaces above that chart. No arbitrary open subset is used.
- The abbreviation `J O_V` in the node is named `I : QuasiCoherentIdeal V`.
  Its defining equality is rendered by `hI`: an epimorphism from `q^*J` onto I
  whose composite with its subobject inclusion is exactly `idealTensorMap q J`.
  This is the standard image characterization of the extended ideal, used also
  by the existing ideal/closed-subspace interfaces. It determines `I.val`
  uniquely, since an epi-mono factorization has exactly that image subobject.
  Thus I is a bound representation of the canonical extended ideal, not an
  additional positivity, flatness, exactness, or existence assumption on q.
  There is no freely chosen map: the existential factorization is normalized
  by the existing canonical tensor map. No separate ideal construction is needed
  to state the assertion with its defining image property.
- `M : CoherentAdicSystem X J hlnX hqcX hqsX` is precisely Coh(X,J).
  Its underlying inverse diagram is `M.obj`.
- `E : V.Modules`, `hEqc`, and `hEcoh` express quasi-coherence and coherent
  Zariski restriction on every etale scheme chart, exactly as in the node.
- The given isomorphism is `β`, between the dependency's termwise tensor-pullback
  diagram and `coherentAdicCompletionDiagram I` applied to E. A natural iso
  between these diagrams is the same iso in the full category of coherent
  adic systems: the target is adic and the property transfers across the iso.
- Coherence of `H = q_*E` is the existential proof `hH`, containing both
  quasi-coherence and coherent scheme-chart restrictions. It is a conclusion,
  never an assumed coherence hypothesis.
- The desired morphism `a` is an actual arrow in `CoherentAdicSystem`, targeting
  `coherentAdicCompletion J hlnX hqcX hqsX` applied to H with that proven hH.
- `CoherentAdicKernelCokernelKilled K a.hom` is the shared boundedness predicate.
  It expands to `∃ t : ℕ, 1 ≤ t ∧ ∀ n`, and annihilates every ordinary ambient
  sheaf kernel and cokernel by `AdicPowerKills K t`. It quantifies their full
  universal properties; it does not take termwise kernels in the adic category.
- The natural comparison κ is a natural transformation from the completion
  diagram of H to the completion diagram of E followed by `moduleDirectImage q`.
  Its first equation is `π_H,n ≫ κ_n = q_*(π_E,n)`. Since π_H,n is the ordinary
  quotient projection, this determines the natural comparison uniquely. Its
  inclusion in the existential only names that canonical map; it strengthens
  neither the hypotheses nor the geometric assertion.
- The last equation is exactly `a_n ≫ κ_n = η_(M_n) ≫ q_*(β_n)`, with η the
  unit of the existing `moduleTensorAdjunction q`. It uses the same a whose
  kernels and cokernels are uniformly annihilated.
- Throughout, `op n` is the node's positive level n+1. No additional level-zero
  condition, finite index set, nonempty space, or nonzero ideal is imposed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentable`, `EtaleSite`, `etaleForget`, `structureSheaf`, `Modules`.
- `def-weil-size-convention`: the existing metatheoretic universe convention,
  implemented with the explicit `universe u` and recorded category/site encoding.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: the existing
  `SheafOfModules.IsQuasicoherent` and its small-etale slice instances; `QCoh`
  is its full subcategory. The module is publicly imported by the adic dependency.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleDirectImage`,
  `moduleTensorPullback`, `moduleTensorAdjunction`, retaining the chart-limit
  normalization. Publicly imported through the ideal dependency.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` publicly exposes
  `WeilConjectures.AlgebraicGeometry.Coherent`, `RingedSpace.IsCoherent`.
  We use this precise finite-type-kernel predicate, not just finite type.
- `Sheaf.AlgebraicGeometry.SpaceCoherentAdicSystem`: `CoherentAdicSystem`,
  `adicQuotientModel`, `coherentAdicCompletionDiagram`, `coherentAdicCompletion`,
  `coherentAdicPullbackDiagram`, `CoherentAdicKernelCokernelKilled`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsProper`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIdeal`:
  `QuasiCoherentIdeal`, `idealTensorMap`.
- The adic module also publicly provides the existing
  `IsAbsolutelyQuasiSeparated`, `schemeRestriction`, `idealSectionImage` and
  point topology, rather than private copies of those notions.

All already recorded proof modules distinct from the statement imports are
imported without `public`. `lem-sfb-space-proper-coherent-higher-images` and
`lem-sfb-scheme-etale-module-exact-finiteness-comparison` have no Lean module in
this checkout; they are only proof prerequisites and therefore have no import.
Their roles are retained explicitly in the full seven-step proof docstring.

Edge cases checked before drafting and again against the final signature:
empty X (and hence V for a morphism to it), zero modules, J=0 (constant quotient
systems), J=O (zero systems), K=0 (only empty charts are outside V(K), and the
positive power condition is vacuous), K=O (q is globally an isomorphism and the
bound requires actual zero kernels and cokernels), non-separated qcqs spaces,
and arbitrary base S. No affine, separated, flat, or nonempty hypothesis was added.

Searches:

- `msearch.py ... leanfinder` with "A proper modification of Noetherian algebraic
  spaces induces a formal adic push pull comparison with kernel and cokernel
  killed by a power of an ideal": eight hits, including `AdicCompletion.map_exact`
  and flatness/completion identities; none is the space statement.
- `msearch.py ... loogle` with `AlgebraicGeometry.AlgebraicSpace, AdicCompletion`:
  no hits; Mathlib has no identifier `AlgebraicGeometry.AlgebraicSpace`.
- `msearch.py ... grep` with
  `adic.*[Pp]ush|[Pp]ush.*[Pp]ull.*[Cc]omparison|[Mm]odification`, restricted to
  Mathlib AlgebraicGeometry: two unrelated elliptic-curve comments.
- `msearch.py ... leansearch` with "proper modification of Noetherian algebraic
  spaces coherent adic systems push pull comparison annihilated by ideal power":
  eight general adic-completion and adic-topology hits, no matching statement.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for the item ID,
  `adic.*[Mm]odification`, `[Mm]odification.*[Pp]ush`, and `formalSystemsPushPull`:
  found the scheme-only FormalSystemsPushPull and FormalSystemsPushPullComparison
  modules and their uses; no existing algebraic-space result.
- `rg` for the proposed declaration name in Mathlib, WeilConjectures, Sheaf, and
  `dag/lean_names_upstream.json`: no existing declaration.
- Read the recorded dependency source signatures and docstrings, including the
  quotient universal property and componentwise annihilation definition.

Validation: scompile.py compiled the module in module mode against the published
server library, both its sandbox name and final module name, with no errors or
unexpected warnings (2.6 s and 2.3 s in the final run).

## Second reading by Q12

This is a second self-check, not an independent-agent review: the dispatcher
explicitly forbids starting other agents. The maintainer performs the independent
review after delivery. Reopened the node and the final Lean file and checked each
binder and conclusion as listed above. Particular checks were that hH remains a
conclusion; hI is an epimorphic image characterization with the correct inclusion;
hU tests all etale charts over the entire complement; β and the final unit use the
same canonical module adjunction; a is a full-subcategory arrow; the bound applies
to ordinary sheaf kernel/cokernel objects at every positive level; κ is normalized
by quotient projections. No mismatch or node fault was found and no source statement
was changed. There are no new or dependency modules to review.
