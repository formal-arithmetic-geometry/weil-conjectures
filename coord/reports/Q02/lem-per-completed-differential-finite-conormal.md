## Worker report

Q02, stage 2, lem-per-completed-differential-finite-conormal. The module
`Sheaf.RingTheory.CompletedDifferentialFiniteConormal` states
`KaehlerDifferential.completed_differential_finite_conormal`, with one `sorry`
and no other declarations. No definitions, new nodes, dependency repairs, or
statement changes are needed. The node copy changes only `lean`.

The earlier dispatch diagnostic confused stages. The Q21 report merged at
coord/ledger.md:41440 explicitly says that it is a stage-1 split, no Lean was
written, and no compiler was run. The current node has no `lean` or
`reviewed_lean` record. This stage-2 delivery uses Q21's accepted seven-step
proof without resplitting or changing any other node field.

Hypotheses and clauses, matched individually:

- The subfield F is `(F : Type u) [Field F]` with `[Algebra F A]`.
  `[IsLocalRing A]` makes A nontrivial, so the algebra map from F is injective.
  Thus the algebra encoding is precisely a specified embedded subfield, with
  no requirement of a coefficient section or residue-field isomorphism.
- The complete Noetherian local ring is `(A : Type v) [CommRing A]`,
  `[IsLocalRing A] [IsNoetherianRing A]`, and
  `[IsAdicComplete (IsLocalRing.maximalIdeal A) A]`.
- The finite residue-field extension is
  `[Module.Finite F (IsLocalRing.ResidueField A)]`; the algebra structure is
  the canonical composite from F through A to its residue field. No
  separability, perfection, characteristic, or finite-type hypothesis is added.
- The module M_F(A) is literally
  `AdicCompletion (IsLocalRing.maximalIdeal A) (KaehlerDifferential F A)`.
  Mathlib's definition is the compatible families of quotients by m^n Omega.
  Its n=0 coordinate is zero and does not change the inverse limit.
- The induced differential d_F(a) is written explicitly as
  `AdicCompletion.of ... (KaehlerDifferential.D F A a)`.
  It is the universal derivation followed by the canonical completion map.
- The first conjunct is `Module.Finite A` of this completion.
- Generation by exact differentials is the next conjunct, `Submodule.span A`
  of the range of the preceding differential equal to top. Together with
  finiteness this also supplies a finite list of exact differential generators.
- The universal clause quantifies over every `N : Type w` with additive group,
  A-module, finite-generation and m-adic completeness instances.
  `[Module F N] [IsScalarTower F A N]` express the restricted scalar action
  needed for Mathlib's derivation type, without restricting the A-modules:
  every A-module has that induced F-action, and the tower forces precisely it.
  `Function.Bijective` is applied to the actual composition map, written
  `(f.comp (AdicCompletion.of ...)).compDer (KaehlerDifferential.D F A)`.
  This reaches all derivations, without a continuity hypothesis. The universes
  u, v, w are explicitly bound and independent.
- Each proper ideal is `∀ (I : Ideal A), I ≠ ⊤ → ...`. Its quotient C is
  literally `A ⧸ I`. The ideal m/I is represented canonically by
  `(IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk I)`, valid since every
  proper ideal of the local ring is contained in m. The first quotient
  conjunct is completeness for exactly this ideal.
- The conormal source is Mathlib's `I.Cotangent`, the quotient I/I^2 with its
  canonical C-module structure. The first arrow `δ` is C-linear, specified
  for every `a : I` by `δ (I.toCotangent a) = 1 tensor d_F(a)`.
- The tensor middle term is `C tensor_A M_F(A)`. It is the source's
  `M_F(A) tensor_A C` via the canonical tensor symmetry. This convention
  puts the scalar algebra first so Mathlib supplies its C-module instance.
  The first-arrow formula is exactly the source formula under that symmetry.
- The second arrow `q` is C-linear into the completion of `Omega[C/F]` for
  the displayed quotient maximal ideal. For every a and c it sends
  `c tensor d_F(a)` to `c • d_F(a mod I)`. The preceding generation clause
  and the tensor generators uniquely specify this arrow. `I.toCotangent`
  is surjective, so the first-arrow formula uniquely specifies δ as well.
  These existential witnesses are characterized canonical maps, not arbitrary
  maps substituted for the arrows in the statement. No choice defines data.
- `Function.Exact δ q` is exactness at the middle term; `Function.Surjective q`
  is exactness at the target followed by zero. No injectivity of δ is asserted.
- The final clause assumes exactly `IsReduced A` and ranges over
  `p ∈ minimalPrimes A`. The instance binder `[p.IsPrime]` exposes the
  primality already implied by that membership; it introduces no additional
  mathematical restriction and allows the fraction-field type to elaborate.
- Its field is literally `FractionRing (A ⧸ p)`. The linear equivalence `e`
  has source `L tensor_A M_F(A)` and target `L tensor_(A/p) M_F(A/p)`.
  Tensor symmetry identifies these with the two written source terms.
  For every a and l, its value is specified as
  `e (l tensor d_F(a)) = l tensor d_F(a mod p)`.
  These elements span the source by the earlier generator clause, so this is
  exactly the canonical map and its being an isomorphism, not the bare
  existence of an unrelated isomorphism. No domain assumption on A is made.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`.
- `Mathlib.RingTheory.AdicCompletion.Basic`, `IsAdicComplete`,
  `AdicCompletion`, and `AdicCompletion.of`.
- `Mathlib.RingTheory.Kaehler.Basic`, `KaehlerDifferential`,
  `KaehlerDifferential.D`, and `KaehlerDifferential.linearMapEquivDerivation`.
  The last universal property underlies the explicit composition expression.
- `Mathlib.RingTheory.Finiteness.Defs`, `Module.Finite`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs/Basic` (publicly available through
  Kaehler.Basic), `TensorProduct`, its pure tensors and tensor symmetry.
  The tensor node is a Mathlib match and needs no replacement lean record.

All recorded proof dependencies with a declaration are imported: Mathlib's
Kaehler.Basic for the ordinary conormal sequence, AdicCompletion.Completeness
for completion completeness, KrullDimension.Zero for the reduced minimal
prime field, TensorProduct.RightExactness for right exactness;
`Sheaf.RingTheory.FiniteOverCompleteRing` for
`Module.finite_and_span_eq_top_of_adicComplete`; and
`WeilConjectures.RingTheory.FiniteModuleComplete` for
`finite_module_complete_over_complete_noetherian`. The latter source was
read via `scompile.py --source` because the older local upstream checkout
lacks that module. Each of the seven accepted proof steps is in the theorem
docstring, including its hypotheses and explicit construction of the
inverse in the conormal universal-property argument.

Source checked directly: sandbox-only pdftotext of EGA-IV-1, printed pp.
151--153, 20.7.14--20.7.15 and 20.7.20, and printed p.177, 21.9.1.
The finiteness lemma allows a finitely generated residual extension; the
node's finite extension is its stated special case. No enlargement was made.

Edge cases checked before writing: A=F and m=0 (ordinary differentials);
A a finite inseparable extension of F (nonzero differentials are allowed);
I=0 (identity quotient sequence); I=m (residue differential sequence);
dual numbers, including characteristic 2; reduced rings with several minimal
primes such as F[[x,y]]/(xy). Reducedness is used only after localizing the
conormal sequence; it does not force I/I^2 to vanish beforehand. The zero
module N and empty lists of generators are included. All proper ideals are
covered; I=top is excluded exactly as in the node. The field universe may
differ from the ring universe, and targets N may be in any universe.
No STATEMENT-DISPUTED flag or mathematical node fault was found.

Searches for reuse (actual msearch results also retained in searches.jsonl):

- LeanFinder: "Completed Kahler differentials of complete Noetherian local
  ring finite residue extension finite module universal derivation conormal
  exact sequence" returned eight hits, headed by `KaehlerDifferential.finite`.
  A second shorter completed-conormal query returned ordinary cotangent
  exactness lemmas. None states this completed theorem. Inspected
  KaehlerDifferential.finite: its EssFiniteType hypothesis is unavailable for
  a general complete local F-algebra, so it cannot replace the item.
- Loogle: "AdicCompletion, KaehlerDifferential", zero hits.
- msearch grep, RingTheory:
  "AdicCompletion.*(Kaehler|Derivation)|(Kaehler|Derivation).*AdicCompletion",
  zero hits.
- LeanSearch: "The adic completion of Kahler differentials of a complete
  Noetherian local algebra with finite residue field extension is finite and
  satisfies the conormal exact sequence" returned AdicCompletion and its
  scalar structures, finite-module completion/tensor equivalences and
  completion exactness. These do not prove finiteness of the completed
  differential module or state this theorem.
- rg in WeilConjectures and lean/Sheaf for completed differentials, completed
  derivations, conormal, and AdicCompletion with KaehlerDifferential; exact-id
  grep in WeilConjectures. No exact declaration. Existing CompletedDifferentials
  is a tensor with the completed ring for Jacobian presentations, a different
  construction; it is not substituted for completion of Omega. The finite
  formal map differential cokernel theorem has a specified formal parameter
  map and residue-field-isomorphism hypotheses; it is not this item.

Validation: prescribed `scompile.py Q02 <item> <module>` compiled both sandbox
and library checks cleanly (2.1 seconds each), with no errors or warnings.
Every variable and universe is explicitly bound. No global build was run.

## Second reading by Q02

A separate reread by the same dispatched worker (no subagents are authorized;
the maintainer supplies the independent review) checked the node against the
complete compiled signature. Every hypothesis and clause is matched above.
In particular I checked that all derivations are quantified without continuity,
that no separability or ordinary differential finiteness is assumed, that the
quotient completion uses the image of m rather than an unrelated ideal, and
that both conormal arrows and the final isomorphism have formulas on all
appropriate generating elements. Tensor symmetry accounts for every factor
order change. Prime membership implies the explicit prime instance, and
restricted F-scalars exist uniquely, so neither typeclass presentation removes
a case. There are no local notations, private definitions or local instances.
No mismatch or statement correction was found on this reread.
