## Worker report

The module `Sheaf.RepresentationTheory.ProfiniteStableLattice` states
`Padic.exists_stable_lattice`, with proof `sorry`, and introduces no definitions.

Hypotheses and clauses correspond as follows:

- Prime ℓ: `(l : ℕ) [Fact l.Prime]`.
- Finite extension E/Qℓ: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`.
- Its valuation ring and maximal ideal: `coefficientExtensionIntegers l E` and
  `coefficientExtensionMaximalIdeal l E` from the recorded dependency.
  `Module.compHom V O.subtype` restricts the given E-module structure to O.
- Compact topological group: `(G : Type v) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]`. No Hausdorff or profiniteness hypothesis added.
- Finite-dimensional vector space: `(V : Type w) [AddCommGroup V] [Module E V]
  [FiniteDimensional E V]`. All three universes are explicit and independent.
- ℓ-adic topology on E: the spectral-norm structure
  `spectralNorm.nontriviallyNormedField ℚ_[l] E`. On V use `moduleTopology E V`.
  In finite dimension over a nontrivially normed field this is the topology transported
  from the finite product E^n by any basis. Thus no arbitrary topology is assumed or
  allowed. The equality is supported by Mathlib's finite-dimensional module-topology
  results and the continuous linear equivalence associated to a basis.
- Homomorphism into GL(V): `ρ : G →* (V ≃ₗ[E] V)`. Linear equivalences are precisely
  invertible E-linear maps, and multiplication is composition.
- Joint continuity: `Continuous (fun p : G × V ↦ ρ p.1 p.2)`.
- Lattice: `∃ Λ : Submodule O V`, `Λ.FG`, and
  `Submodule.span E (Λ : Set V) = ⊤` express finite generation and E-spanning.
- Necessary freeness and rank: `Module.Free O Λ` and
  `Module.finrank O Λ = Module.finrank E V`.
- Stability with equality, not only inclusion:
  `∀ g : G, (ρ g) '' (Λ : Set V) = (Λ : Set V)`.
- Topology equality: `(coefficientExtensionMaximalIdeal l E).adicModuleTopology Λ =
  TopologicalSpace.induced (fun x : Λ ↦ (x : V)) inferInstance`.
  Mathlib's `Ideal.adicModuleTopology` uses the neighborhood basis m^n Λ.
- Restricted action: with the adic topology installed on Λ, a function
  `a : G × Λ → Λ` is continuous and satisfies
  `∀ p, (a p : V) = ρ p.1 (p.2 : V)`. This specifies exactly the restricted action;
  subtype injectivity makes it unique and supplies all action identities automatically.
  Existentially specifying the restriction avoids choosing membership proofs in the signature.

The recorded dependency module is `Sheaf.NumberTheory.Padics.CoefficientExtension`:
`Padic.coefficientExtensionIntegers` and `Padic.coefficientExtensionMaximalIdeal` were
read with their full signatures and docstrings. Its spectral absolute value is exactly
that used by the spectral-norm field topology here. Other APIs used are Mathlib's
`moduleTopology`, `Ideal.adicModuleTopology`, `Submodule.FG`, `Submodule.span`,
`Module.Free`, and `Module.finrank`. No additional definition or dependency module is needed.

Source checked online because literature/stanford-weil2-seminar is absent on this machine:
[Stanford lecture 19, Proposition 1.1.9](https://math.stanford.edu/~conrad/Weil2seminar/Notes/L19.pdf),
the second bullet and the finite-translate stable-lattice argument. The node's compact-group
version uses only compactness to obtain the finite coset cover.

Edge cases checked: V=0 gives Λ=0, free rank zero, with the unique topology and action;
trivial G imposes no further restriction; nonfaithful actions are allowed; arbitrary compact
G is allowed, including non-Hausdorff groups; no positive dimension or positive rank is
assumed. Every prime ℓ is permitted. The adic topology includes n=0 (the whole module),
which is a harmless neighborhood. No choice of initial basis is a hypothesis.

Searches (run through msearch.py with group E1 and this item):

- LeanSearch: `continuous representation of compact group preserves a lattice over p-adic integers`;
  unavailable, Internal Server Error, recorded as unavailable.
- LeanFinder: the same query; eight hits concerning cyclotomic characters, compact p-adic
  integers, proper p-adic numbers and Mahler expansions, no stable-lattice result.
- Loogle: `Submodule.FG, Continuous`; zero hits.
- Mathlib grep: `stable.lattice|invariant.lattice|exists_lattice`; zero hits.
- Source repository rg: `Lattice|lattice|adicModuleTopology` in RepresentationTheory;
  `PadicAlgCl.exists_lattice_of_forall_mem` is a different statement: representations over
  an algebraic closure with bounded coefficients in an intermediate field, and finite
  images on quotients, rather than arbitrary finite E with a jointly continuous action
  and equality of topologies. Read its full signature and docstring in IntegralModel.lean.
- Source repository rg for `lem-pod-profinite-stable-lattice`: zero hits.
- Project rg for `lattice|Lattice|IsModuleTopology`: only unrelated categorical lattices.
- Collision search for `exists_stable_lattice|exists_invariant_lattice` in upstream names,
  Mathlib, source repository and lean/Sheaf: zero hits.

No node faults or statement disputes found. No statement correction or new nodes.

## Second reading by E1

I independently read the sandbox node and all 59 lines of its module, the dependency
node `def-weil-l-adic-coefficient-extension`, its recorded module
`Sheaf.NumberTheory.Padics.CoefficientExtension`, and the supporting
`Padic.extension_integers_dvr` signature. The statement matches the node; no Lean
or node changes are needed. This delivery contains no new definition nodes or
replacement dependency modules and has no statement correction.

Source: I opened Stanford lecture 19, Proposition 1.1.9, second bullet, printed
page 3, https://math.stanford.edu/~conrad/Weil2seminar/Notes/L19.pdf.
The surrounding proposition concerns sheaves on a geometrically connected scheme;
that hypothesis serves the sheaf/representation correspondence, not the abstract
stable-lattice argument extracted here. The argument uses an open stabilizer and
finitely many cosets. Compactness supplies the latter for the node's general
compact topological group, without a Hausdorff or total-disconnectedness assumption.
The adjacent third bullet uses maximal-ideal powers on the resulting lattice.
No Stacks tag is the source of this item.

Object, hypothesis, and conclusion checklist (each verdict: matches):

1. A prime ell: `(l : ℕ) [Fact l.Prime]`; neither ell=2 nor any other prime is excluded.
2. A finite extension E/Q_ell: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
   [FiniteDimensional ℚ_[l] E]`. A field algebra over Q_ell is an injective field
   extension; no separability, normality, chosen embedding into an algebraic closure,
   or extra topological instance is assumed.
3. Its integer ring O_E and maximal ideal m_E: `let O := coefficientExtensionIntegers
   l E` and `coefficientExtensionMaximalIdeal l E`, from the dependency's recorded
   declarations. Reading the choices and `extension_integers_dvr` confirms membership
   is exactly absolute value <=1 and <1 respectively. The norm is the spectral norm
   extending the Q_ell norm. These are not arbitrary subrings or ideals.
4. A compact topological group G: `(G : Type v) [Group G] [TopologicalSpace G]
   [IsTopologicalGroup G] [CompactSpace G]`. These are exactly the stated group,
   continuous multiplication/inverse, and compactness conditions; no profiniteness
   instance, finiteness, faithfulness, or Hausdorff assumption is added.
5. A finite-dimensional E-vector space V: `(V : Type w) [AddCommGroup V]
   [Module E V] [FiniteDimensional E V]`. Its O_E-module structure is the restriction
   `Module.compHom V O.subtype`, so the submodules really lie in the given V.
6. Its ell-adic topology: the local instance
   `spectralNorm.nontriviallyNormedField ℚ_[l] E` gives the same absolute value as
   the dependency, and `letI : TopologicalSpace V := moduleTopology E V` gives
   the finite-dimensional vector-space topology. I read Mathlib's `moduleTopology`,
   `IsModuleTopology.iso`, the finite-product instances, and the finite-dimensional
   basis continuity results. Transporting the product topology on E^n by a basis
   gives an IsModuleTopology instance, hence equals moduleTopology. No arbitrary
   topology on V, or extra normed-space assumption, appears in the signature.
7. A homomorphism rho into GL_E(V): `∀ (ρ : G →* (V ≃ₗ[E] V))`; linear equivalences
   are the invertible E-linear endomorphisms with composition as multiplication.
   This rho is quantified before the lattice, as in the node.
8. Joint continuity: `Continuous (fun p : G × V ↦ ρ p.1 p.2) →`; this is precisely
   the stated action map, not merely separate continuity or continuity of orbit maps.
9. Existence of an O_E-lattice: `∃ Λ : Submodule O V`, with `Λ.FG` and
   `Submodule.span E (Λ : Set V) = ⊤`. These are finite generation and E-spanning.
10. Necessary freeness and rank: `Module.Free O Λ` and
    `Module.finrank O Λ = Module.finrank E V`; both are included explicitly.
11. Stability for every g: `(∀ g : G, (ρ g) '' (Λ : Set V) = (Λ : Set V))`.
    Set image equality is exactly rho(g)Lambda=Lambda, including the reverse inclusion.
12. Equality of topologies: `(coefficientExtensionMaximalIdeal l E).adicModuleTopology
    Λ = TopologicalSpace.induced (fun x : Λ ↦ (x : V)) inferInstance`.
    Mathlib's definition uses the submodules m_E^n times the whole Lambda, not powers
    in the ambient V; the right side is the topology induced from this V.
13. Continuity of the restricted action for the adic topology: after installing that
    topology, `∃ a : G × Λ → Λ, Continuous a ∧ ∀ p : G × Λ,
    (a p : V) = ρ p.1 (p.2 : V)`. The final equality specifies the unique restriction
    by subtype injectivity. It implies the action identities from rho, so existential
    presentation of the restriction neither weakens nor strengthens this clause.

Edge cases: V=0 allows Lambda=0, free of rank zero, with the unique topology and
restricted action. The basis/product comparison includes an empty basis. G cannot
be empty because it is a group; the trivial group and non-Hausdorff compact groups
are allowed. Empty schemes are irrelevant to this abstract statement. All primes
are allowed, and E necessarily has characteristic zero. The n=0 neighborhood in the
adic topology is the whole module and imposes no positive-rank condition. Universes
u, v, w are explicitly bound and independent; there is no smallness restriction on
G or V. All variables are bound in the theorem or its local lets.

Independent searches, using different terms from the first reading:

- LeanSearch via msearch.py: `compact topological group representation over finite
  extension of Qp admits invariant lattice`; service returned Internal Server Error,
  recorded unavailable rather than a no-match verdict.
- LeanFinder via msearch.py: `compact group p-adic linear action invariant finitely
  generated integral submodule`; eight hits, including real Z-lattices,
  `Algebra.IsInvariant.isIntegral_of_profinite`, and `Submodule.isCompact_of_fg`;
  none states this result.
- Loogle via msearch.py: `Module.Free, Submodule.FG`; two hits about finite
  presentations, neither about stable lattices.
- Independent rg of all Mathlib, WeilConjectures, and project lean/Sheaf for
  `invariant.*lattice|lattice.*invariant|stable.*lattice|lattice.*stable|exists_lattice`.
  Mathlib hits concern order lattices and real lattices, not this statement. I opened
  the full signatures and docstrings of `PadicAlgCl.exists_lattice_of_forall_mem`
  in RepresentationTheory/IntegralModel.lean and `WeilGroup.IsLisse.exists_lattice`
  in EtaleCohomology/Purity/RealSheaves/LocalSystems.lean. The former assumes a basis
  over PadicAlgCl with matrix coefficients bounded in an intermediate field; the
  latter assumes a lisse Weil representation and restriction along a nonempty open
  subscheme. Both conclude finiteness on quotient images and neither states the
  arbitrary E-vector-space result with the two topology/continuity clauses here.
- Collision search for `exists_stable_lattice` in dag/lean_names_upstream.json,
  Mathlib, WeilConjectures, and lean/Sheaf found no existing declaration.

H5/H6/H8/H9: no definitions or instances are introduced by the module, so there
is no hollow data. Its sole theorem has proof `by sorry`. Module and declaration
docstrings name the source and this blueprint id. The proof docstring carries all
four node steps, including the open-stabilizer and DVR dependencies, the finite coset
cover, inverse argument for stability equality, and basis comparison of topologies.
The namespace is Padic without a Sheaf prefix, imports are used, and lines meet the
100-character convention. The node's lean.statement is verbatim the signature.

Mismatches found: none. Changes: appended this independent second-reading report;
left the Lean statement, node, and Worker report unchanged. Validation: scompile.py
compiled the module on the server in 1.8 seconds, exit code 0, with no warnings.
