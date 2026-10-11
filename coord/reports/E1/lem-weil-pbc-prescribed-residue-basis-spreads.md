## Worker report

The module `Sheaf.RingTheory.PrescribedResidueBasisSpreads` states
`Module.FinitePresentation.exists_basis_away_of_prescribed_residue_basis`; its only proof
is `sorry`. No definitions, new nodes, dependency modules, or statement corrections are needed.

The node's hypotheses and conclusion correspond as follows:

- A commutative ring A: `{A : Type u} [CommRing A]`.
- An A-module M: `{M : Type v} [AddCommGroup M] [Module A M]`.
- A finite presentation (the existence of a finite generators-and-relations sequence):
  `[Module.FinitePresentation A M]`, Mathlib's finite-presentation class.
- A prime ideal p: `(p : Ideal A) [p.IsPrime]`.
- The r prescribed elements: `(r : ℕ) (m : Fin r → M)`; zero-based indexing merely
  renames the node's indices 1 through r.
- Their residue images form a basis: `hres` asserts existence of a
  `Basis (Fin r) p.ResidueField (p.ResidueField ⊗[A] M)` whose ith element equals
  `(1 : p.ResidueField) ⊗ₜ[A] m i`. The dependency explicitly records the scalar-first
  tensor encoding; `TensorProduct.comm` identifies it with M ⊗ κ(p), sending these
  elements to m_i ⊗ 1. This is the same base change, with its κ(p)-module structure.
- M_p is free of rank r: `hfree : Nonempty (Basis (Fin r) (Localization.AtPrime p)
  (LocalizedModule p.primeCompl M))`. A finite basis of exactly r elements is equivalent
  to the node's free-of-rank-r hypothesis over this nontrivial local ring.
- There is f outside p: `∃ f : A, f ∉ p ∧ ...`.
- The images of the SAME elements form an A_f-basis of M_f: the resulting basis is
  `Basis (Fin r) (Localization.Away f) (LocalizedModule.Away f M)`, and each `b i`
  equals `LocalizedModule.mkLinearMap (Submonoid.powers f) M (m i)`, exactly m_i/1.

Dependency declarations read and used:

- def-weil-pbc-module-localization: Mathlib.Algebra.Module.LocalizedModule.Basic,
  `LocalizedModule` and `LocalizedModule.mkLinearMap`.
- def-weil-pbc-localization-at-prime: Mathlib.RingTheory.Localization.AtPrime.Basic,
  `Localization.AtPrime`; Mathlib.RingTheory.LocalRing.ResidueField.Ideal,
  `Ideal.ResidueField`.
- def-weil-pbc-module-localization-away: Mathlib.Algebra.Module.LocalizedModule.Basic,
  `LocalizedModule.Away`; `Localization.Away` is the associated scalar ring.
- def-weil-pbc-free-module: Mathlib.LinearAlgebra.FreeModule.Basic, `Module.Free` and
  the `Module.Basis` notion underlying its `exists_basis` field. The fixed finite rank
  is expressed directly by a `Basis (Fin r)` rather than unspecified-rank freeness.
- def-weil-module-base-change: Mathlib.LinearAlgebra.TensorProduct.Tower,
  `TensorProduct` and its left module structure, with elements expressed by `tmul`.
  The recorded `LinearMap.baseChange` concerns maps; no base-changed linear map is
  needed to state this node.

The imports bring in the recorded definitions transitively where appropriate; the tensor
Tower import supplies the scalar-extension module infrastructure and Localization.Free
supplies localization module structures, bases, and finite presentation.

Edge cases checked: r=0 is included; the empty basis hypothesis means the corresponding
module vanishes, and spreading gives zero M_f. M=0 has a residue basis only for r=0.
The zero ring has no prime ideal, so the hypotheses are impossible, as in the node.
No Noetherian, domain, flatness, or positive-rank hypotheses were added. Ring and module
universes are independent and both explicit; localization and tensor products use their
maximum, excluding no modules. For f outside p, f is not nilpotent; no separate condition
on f is needed. No mathematical dispute found.

Source read: the local literature/stacks-project/algebra.tex is absent on this machine;
the cited original proof was read at https://stacks.math.columbia.edu/tag/0GWM.
Its map from a finite free module, followed by shrinking its isomorphism locus, is the
node's proof route. The module docstring includes all five DAG proof steps and their
named dependencies, including the prescribed-lift Nakayama and endomorphism arguments.

Searches (via /home/ubuntu/weil-launcher/msearch.py, group E1, this item):

- leansearch: "finitely presented module prescribed residue basis spreads to basis of
  localization away". UNAVAILABLE: service Internal Server Error; no verdict attributed
  to this unavailable search.
- leanfinder: "prescribed elements of a finitely presented module whose residues are a
  basis and localization at a prime is free of the same rank form a basis after localization
  away from an element outside the prime". Eight hits, notably
  `Module.FinitePresentation.exists_basis_localizedModule_powers`,
  `Module.exists_basis_of_basis_baseChange`, and `Module.Basis.ofIsLocalizedModule`.
  None gives the exact prescribed-global-elements conclusion with these hypotheses.
- loogle: "Module.FinitePresentation, Module.Basis, LocalizedModule". One hit:
  `Module.FinitePresentation.exists_basis_localizedModule_powers`; full signature and
  docstring read in Localization/Free.lean. Its output basis merely lifts the given
  prime-local basis and need not equal the specified global elements divided by 1.
- grep through msearch, RingTheory:
  "exists_basis_localizedModule_powers|exists_basis_of_basis_baseChange|basis.*residue".
  Four hits in Localization/Free.lean and LocalRing/Module.lean, no exact match.
- rg on WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json:
  "prescribed.*basis|residue.*basis.*spread|exists_basis_localizedModule_powers|lem-weil-pbc-prescribed-residue-basis-spreads".
  Only the unrelated polynomial quotient-basis module matched; no existing declaration.

Validation: server single-file compilation and the deliver2.py --no-push dry run are run
for this delivery; the second reader supplies the independent second reading and delivers.

## Second reading by E1

I independently read the node, its Stacks source place (Algebra, proof of Tag
0GWM), the dependency records, and
`Sheaf/RingTheory/PrescribedResidueBasisSpreads.lean`.

The node's objects and hypotheses match the Lean as follows:

- A commutative ring (A) is `{A : Type u} [CommRing A]`.
- An (A)-module (M) is `{M : Type v} [AddCommGroup M] [Module A M]`.
- Finite presentation is `[Module.FinitePresentation A M]`.
- A prime ideal is `(p : Ideal A) [p.IsPrime]`.
- The finite family of prescribed elements is `(r : ℕ) (m : Fin r → M)`.
- The residue-field basis hypothesis is `hres : ∃ b : Basis (Fin r)
  p.ResidueField (p.ResidueField ⊗[A] M), ∀ i, b i =
  (1 : p.ResidueField) ⊗ₜ[A] m i`.  Mathlib's scalar-first tensor encoding is
  canonically `TensorProduct.comm`-equivalent to the node's (M\otimes_A
  \kappa(p)) notation; the dependency record explicitly records this
  convention, so the represented notion and prescribed elements agree.
- Freeness of rank (r) at (p) is
  `hfree : Nonempty (Basis (Fin r) (Localization.AtPrime p)
  (LocalizedModule p.primeCompl M))`, exactly a basis indexed by `Fin r`.
- The conclusion's element is `f : A` with `f ∉ p`; its basis is
  `b : Basis (Fin r) (Localization.Away f) (LocalizedModule.Away f M)` and
  the prescribed equality is
  `b i = LocalizedModule.mkLinearMap (Submonoid.powers f) M (m i)` for every
  `i`, which is precisely (m_i/1) in (M_f).

No hypothesis is added: there is no Noetherian, domain, flatness, or rank
positivity assumption, and the quantifier order agrees with the node. The
conclusion has exactly the existential `f`, the non-membership condition, the
basis, and the pointwise prescribed-image clause.

Edge cases were checked. `r = 0` gives the empty basis and includes the zero
module case; the zero ring has no prime ideal, so its impossible-hypothesis case
is covered. Independent explicit universes permit all module/ring universe
sizes. No characteristic or nonempty-index assumption is present or needed.

I searched Mathlib, `WeilConjectures`, and `lean/Sheaf` for the notion and for
variants of the statement (including `exists_basis_localizedModule_powers`,
`exists_free_localizedModule_powers`, `exists_basis_of_basis_baseChange`, and
prescribed/residue-basis names). These searches found no exact existing
statement; the Mathlib results do not force the prescribed global elements.
The source repository has no matching declaration. Thus the module is new.

The only potential presentational mismatch is tensor-factor order in `hres`:
Lean's `Basis` needs the scalar-first module `p.ResidueField ⊗[A] M`, while the
node writes (M\otimes_A\kappa(p)). The canonical commutation isomorphism,
recorded by `def-weil-module-base-change`, makes these the same base-change
notion and preserves the specified elements under the corresponding map; no
statement change is required. No other mismatch was found and no source or
node repair was necessary.

Compilation with `scompile.py` succeeds with only the permitted `sorry`
warning. The module has no hollow definitions and its theorem docstring gives
all five proof steps and their cited dependencies.
