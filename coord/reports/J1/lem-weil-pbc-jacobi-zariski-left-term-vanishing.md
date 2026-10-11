## Worker report

The module `Sheaf.RingTheory.JacobiZariskiLeftTermVanishing` states
`Algebra.jacobiZariski_leftTerm_vanishing`, with a sorry proof and no new definitions.

Hypothesis and clause correspondence:
- The commutative ring homomorphism A → B is represented by `(A : Type u) (B : Type v)`
  with `[CommRing A] [CommRing B] [Algebra A B]`. This includes every ring map by its
  `RingHom.toAlgebra`, with no injectivity, finiteness or nontriviality restriction.
- H₁(L_{B/A}) = 0 is `[Subsingleton (H1Cotangent A B)]`.
- Projectivity of Ω_{B/A} is `[Module.Projective B (KaehlerDifferential A B)]`.
- The ideal is `(a : Ideal B)`; C is written directly as `B ⧸ a`.
- The canonical presentation and its two-term complex are
  `P := (Generators.self A B).toExtension`, with differential `P.cotangentComplex`.
  Its domain is `P.Cotangent` = I/I². Its codomain `P.CotangentSpace` is
  B ⊗[A[B]] Ω[A[B]/A], the canonical model of the free B-module on d[b].
  The universal differential gives precisely the partial-derivative map in the node.
- `δ := P.cotangentComplex.rTensor (B ⧸ a)` is δ ⊗ id_C on N₁ ⊗ C → N₀ ⊗ C.
  The degree-one homology of this two-term complex is `LinearMap.ker δ`.
- `ι := P.h1Cotangentι.rTensor (B ⧸ a)` is the tensor of the actual kernel inclusion.
  `Function.Injective ι` is the first assertion of the final sentence;
  `LinearMap.range ι = LinearMap.ker δ` is its image assertion.
- `Nonempty ((LinearMap.ker δ) ≃ₗ[B] (H1Cotangent A B ⊗[B] (B ⧸ a)))`
  states the displayed isomorphism of B-modules. Both sides have their natural
  quotient-module interpretation; the injective inclusion and image equality already
  identify them canonically. Since both are zero there is no distinction between a
  B-linear and a C-linear isomorphism here.
- The last two `Subsingleton` conjuncts state respectively H₁(L) ⊗ C = 0 and
  H₁(NL ⊗ C) = 0.

Dependency declarations read and used:
- `def-weil-pbc-smooth-ring-map` is a Mathlib leaf. Its record explicitly identifies
  `Algebra.H1Cotangent` in `Mathlib.RingTheory.Extension.Cotangent.Basic`, defined as
  `(Generators.self A B).toExtension.H1Cotangent`. The same module defines the differential,
  kernel and kernel inclusion (`Algebra.Extension.cotangentComplex`,
  `Algebra.Extension.H1Cotangent`, `Algebra.Extension.h1Cotangentι`).
  `Algebra.Generators.self` in `Mathlib.RingTheory.Extension.Generators` is the polynomial
  presentation on every element of B, with `val := id`.
  The recorded `Algebra.Smooth` signature and docstring in
  `Mathlib.RingTheory.Smooth.Basic` were read; smoothness is not assumed in this node,
  so no smoothness instance or finite-presentation hypothesis is introduced.
- `def-weil-pbc-kahler-differentials` records `KaehlerDifferential` in
  `Mathlib.RingTheory.Kaehler.Basic`; its full definition, universal derivation `D`,
  and universal-property equivalence `linearMapEquivDerivation` were read.
  These declarations are imported transitively through Cotangent.Basic.
- `LinearMap.rTensor` in `Mathlib.LinearAlgebra.TensorProduct.Map` supplies tensoring
  on the right, matching the node's tensor order.

Source checked: local Stacks sources are absent on this machine, so the final assertion
and complete proof of https://stacks.math.columbia.edu/tag/00S2 were opened directly.
They give exactly the two short exact sequences in the node. The theorem docstring
includes all four proof steps and their DAG references.

Edge cases checked mathematically before writing: a = ⊤ makes C the zero ring, so both
source and kernel tensors vanish; a = ⊥ gives the original injective differential;
zero A or B is allowed. No properness of a, nonzero-ring hypothesis, finite presentation,
finite generation of Ω, or flatness of C is assumed. Independent explicit universes u,v
allow arbitrary ring universes; the canonical polynomial presentation lives in max u v.
No auto-implicit parameters are used.

Searches (all remote Mathlib searches made through msearch.py):
- LeanSearch: `tensor base change naive cotangent complex kernel vanishes projective differentials`.
  Service returned Internal Server Error; logged as unavailable.
- LeanFinder: `H1 of naive cotangent complex tensor quotient vanishes when H1 zero and Kaehler differentials projective`.
  Eight results, including Algebra.formallySmooth_iff, H1Cotangent, and
  Algebra.Extension.tensorH1Cotangent. None states this tensor-kernel assertion.
- Loogle: `Algebra.Extension.cotangentComplex`. Twelve results: differential, H1 kernel,
  kernel inclusion/exactness and maps; no quotient tensor vanishing theorem.
- Mathlib grep: `cotangentComplex.*(Tensor|tensor)|lTensor.*ker` in RingTheory.
  Found flat base-change statements, tensor-kernel statements requiring a flat tensor factor,
  and cotangent base-change comparisons; none supplies the present projective-cokernel case.
- rg in both WeilConjectures and lean/Sheaf, and in dag/lean_names_upstream.json:
  `left.term.vanishing|cotangentComplex.*rTensor|h1Cotangentι.*rTensor`: no hits.
- grep in WeilConjectures for this item's exact blueprint id: no hits.
- Earlier broad cotangentComplex/H1Cotangent search in both project RingTheory directories
  found SubsingletonH1CotangentOfCharP and GeometricallyRegularH1Injective, neither a match.

No node correction, new node, dependency replacement or disputed statement is needed.
Server scompile.py compiled the module cleanly (exit 0, 1.4 seconds).

## Second reading by J1

I reread the node statement, its Stacks source (Algebra, Tag 00S2, final assertion and proof), and the module declaration item by item.

- Objects: the node's commutative rings and algebra map (A\to B) are `(A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]`; no injectivity, finite presentation, Noetherian, nonzero, or flatness hypothesis is added. `H1Cotangent A B` is Mathlib's canonical first cotangent homology for `Generators.self A B`, and `[Subsingleton (H1Cotangent A B)]` renders (H_1(L_{B/A})=0). `KaehlerDifferential A B` with `[Module.Projective B ...]` renders projective (Omega_{B/A}). The ideal (mathfrak a) is `(a : Ideal B)` and (C=B/\mathfrak a) is `B ⧸ a`.
- Complex: `P := (Generators.self A B).toExtension`; `P.cotangentComplex` is the canonical (N_1=I/I^2\to N_0=\bigoplus_{b\in B}B\,d[b]), and `δ := P.cotangentComplex.rTensor (B ⧸ a)` is exactly (δ\otimes\mathrm{id}_C). Thus `LinearMap.ker δ` renders (H_1(\mathrm{NL}_{B/A}\otimes_B C)).
- More precise clause: `ι := P.h1Cotangentι.rTensor (B ⧸ a)` is the map induced by (ker δ\subseteq N_1). `Function.Injective ι` and `LinearMap.range ι = LinearMap.ker δ` render the asserted injectivity and image. The `Nonempty` linear equivalence renders (\ker(δ\otimes C)\cong H_1(L_{B/A})\otimes_B C). The two final `Subsingleton` clauses render both displayed zero modules.
- Quantifier order and universes agree; `u,v` are independent and no variable is implicit or unbound.

Edge cases checked: `a = ⊤` gives the zero quotient and both tensor modules are zero; `a = ⊥` gives the untensored inclusion; zero rings are admitted; no characteristic or finiteness assumption is present; arbitrary index set (B) in the canonical presentation is covered.

Searches were independently checked in Mathlib and the source project: LeanSearch for projective tensor/cotangent-kernel vanishing (service unavailable), LeanFinder for the same concept (only general cotangent/formally-smooth declarations), Loogle for `Algebra.Extension.cotangentComplex` (no quotient-kernel theorem), and `rg`/grep for `left.term.vanishing`, `cotangentComplex.*rTensor`, and `h1Cotangentι.*rTensor` (no existing project declaration). The recorded dependency declarations were read in `Mathlib.RingTheory.Extension.Cotangent.Basic` and `Mathlib.RingTheory.Kaehler.Basic`; they are the notions named by the dependencies.

No mismatch was found. I changed no statement, hypotheses, dependencies, or definition. The module compiles with `scompile.py` (exit code 0; only the permitted `sorry` proof remains).
