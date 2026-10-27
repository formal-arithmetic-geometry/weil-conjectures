## Worker report

This is a stage-2 statement delivery, not a new stage-1 split. The current node has
reviewed Q05 stage-1 work but no Lean record; coord/queue.tsv puts it in stage 2.
The inherited BLOCKED ending concerned a second split. The stage-handoff paragraph
in coord/brief-stage2.md explicitly authorizes proceeding with deliver2.py here.
The accepted statement, seven proof steps, and proof dependencies are preserved.
Only lean and the addition of the elementary-group definition to stmt_deps change.

The main module states Representation.brauer_elementary_unit_character, with sorry
as its entire proof. The definition module constructs Group.IsBrauerElementary as
an explicit predicate, with no postponed data or subsidiary theorem.

Hypotheses and clauses, matched individually:

- A finite group G is `(G : Type u) [Group G] [Finite G]`. No Fintype,
  decidable equality, nontriviality, or restriction on the group universe is added.
- The coefficient field is the usual `ℂ`, not an arbitrary field with an extra
  assumed property. The algebraically closed characteristic-zero facts are facts
  about this field, not hypotheses on the group or representations.
- Finitely many subgroup/representation/coefficient terms are given by `n : ℕ`
  and the common index type `Fin n`. Repeated subgroups are allowed, just as in a
  finite family; no distinctness condition is imposed.
- `E : Fin n → Subgroup G` supplies the actual subgroups of G.
- Elementary means `(∀ i, Group.IsBrauerElementary (E i))`. Unfolding the definition,
  each E has its own prime `p` and exponent `a : ℕ`, so neither is required to be
  uniform over the family. `p.Prime`, `IsCyclic C`, `(Nat.card C).Coprime p`,
  `Nat.card P = p ^ a`, and `Nonempty ((C × P) ≃* E)` give each stated clause.
  Finite factors follow because C and P are subgroups of the finite group E.
  Taking the factors to be subgroups loses no abstract product presentation:
  transport the two factors to their images under an isomorphism C×P≃E.
  Conversely any two such subgroups and the product isomorphism give the abstract
  finite groups required by the statement. The isomorphism is an actual group
  isomorphism; no compatibility with subgroup multiplication is imposed.
- `W : Fin n → ModuleCat.{v} ℂ` gives arbitrary complex vector spaces, with
  `(∀ i, Module.Finite ℂ (W i))` stating precisely finite-dimensionality over ℂ.
  Their universe v is independent of u. These are the actual spaces, not fixed
  dimension matrix models. The bundled additive-group and module structures are
  the vector-space structures used by the representation and trace.
- `ρ : (i : Fin n) → Representation ℂ (E i) (W i)` gives the linear action.
  Since E i is a group, every action map is invertible, with inverse the map of
  the inverse element; this is equivalent to the node's linear group action.
- The induction object is the existing `Representation.IndV (E i).subtype (ρ i)`;
  its group action is `Representation.ind (E i).subtype (ρ i)`. Mathlib's generator
  at x has right-inverse translation; the node's `[g,w]` is its generator at g⁻¹.
  The diagonal coinvariant relation gives `[ge,w]=[g,ρ(e)w]`, while ind_mk sends
  `[g,w]` to `[ag,w]`. The inverse sends the generator at x to `[x⁻¹,w]`. Thus the
  quotient and action are exactly the node's, not a coinduced or dual character.
- Each induced character is exactly `LinearMap.trace ℂ (IndV ...) (ind ... g)`.
  IndV is finite-dimensional here because G is finite and W i is finite-dimensional:
  it is a quotient of ℂ[G] tensor W i. Trace itself does not require adding a
  typeclass binder for that consequence.
- `a : Fin n → ℤ` admits negative coefficients. `(a i : ℂ) * ...` is the integer
  multiple of the complex trace, equivalently integer scalar multiplication.
- `∀ g : G, (1 : ℂ) = ∑ i, ...` is the equality of functions on G, evaluated at
  every element. The left side is the constant unit character, not an indicator.

Dependency declarations read and used:

The sole original statement dependency, def-weil-algebraic-closure, has no lean
record because it is a Mathlib leaf. Its mathlib_match is AlgebraicClosure in
Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure, together with IsAlgClosed and
IsAlgClosure in Mathlib.FieldTheory.IsAlgClosed.Basic and IsAlgClosure.equiv.
The node means that ℂ is algebraically closed, so the relevant part is IsAlgClosed,
not a fresh choice of algebraic closure. Its full class signature/docstring were
read, as were the IsAlgClosure class and AlgebraicClosure construction. The main
module imports IsAlgClosed.Basic for the proof plan and
Mathlib.Analysis.Complex.Polynomial.Basic for Complex.isAlgClosed.

The additional statement dependency is def-per-brauer-elementary-group, defined
by Group.IsBrauerElementary in Sheaf.GroupTheory.BrauerElementary.
The remaining notions use Mathlib directly: Group, Finite, Subgroup, IsCyclic,
Nat.card, Nat.Coprime, Nat.Prime, MulEquiv, ModuleCat, Module.Finite,
Representation, Representation.IndV, Representation.ind, and LinearMap.trace.
The full quotient/action implementation and generator convention in
Mathlib.RepresentationTheory.Induced were read; the same convention is already
recorded by the landed induced-character node.

Stated proof dependencies are imported without public:

- lem-per-cyclotomic-integer-power-basis: IsPrimitiveRoot.integralPowerBasis and
  its generator/dimension statements in Mathlib.NumberTheory.NumberField.Cyclotomic.Basic;
  primitive roots from Mathlib.RingTheory.RootsOfUnity.Complex.
- lem-per-finite-group-induction-calculus:
  Rep.QuotientInduction.finiteGroupInductionCalculus, ind, res, and mk in
  Sheaf.RepresentationTheory.FiniteGroupInductionCalculus. The main signature
  and concrete generator definitions were read. Its FDRep convenience interface
  uses a common universe for field and group, so the present statement uses its
  underlying Mathlib induction construction directly to retain independent
  group and coefficient-module universes. No dependency repair is needed.
- lem-weil-complex-algebraically-closed: Complex.isAlgClosed, as above.
- lem-weil-pbc-sylow-subgroup-prime-index: Sylow.nonempty, Sylow.isPGroup', and
  Sylow.not_dvd_index, via Mathlib.GroupTheory.Sylow.
- lem-per-induced-character-conjugacy-formula:
  Representation.induced_character_conjugacy_formula in
  Sheaf.RepresentationTheory.InducedCharacterConjugacyFormula. Its module and
  full signature/docstring were read, including both equalities and universe binders.
- lem-per-finite-group-character-decomposition:
  IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp in
  Mathlib.RingTheory.SimpleModule.Basic.
- lem-per-finite-group-character-orthogonality: FDRep.char_orthonormal in
  Mathlib.RepresentationTheory.Character.

lem-per-character-prime-part-reduction and
lem-per-finite-function-subring-residue-test have no recorded Lean declaration
or Mathlib match at the time of this delivery. They are proof-only inputs, not
needed objects in this statement, and remain named explicitly in its proof docstring.
No import for either can yet be included. No import cycle is introduced.

Edge cases checked before writing:

- Trivial G is allowed. It is elementary using p=2 and both factors trivial,
  and its trivial line supplies the identity with one term and coefficient 1.
- The trivial cyclic factor and exponent a=0 are allowed. There is no positivity
  condition on a, on the cyclic order beyond the automatic group nonemptiness,
  or on a representation dimension. In particular all p-groups and cyclic groups
  have the intended possibilities.
- Zero W is permitted and its induced character is zero. No nonzero or
  irreducibility assumption was added.
- n=0 is allowed as a candidate index type; its sum is zero and cannot witness
  the conclusion because every group has an identity and 1≠0 in ℂ. The theorem
  is existential and need not assert positivity separately.
- Negative and zero coefficients remain allowed. The equality is at every g,
  including the identity where it becomes the required dimension identity.
- Arbitrary group/module universes remain independent. Factor subgroups are a
  universe-independent encoding of the abstract product decomposition.
- p=0 and p=1 are excluded exactly by p.Prime. No fixed prime is chosen globally.

Searches made:

msearch.py leanfinder query “The trivial complex character of a finite group is an
integer linear combination of characters induced from elementary subgroups” returned
8 hits, including FDRep.char_orthonormal, FDRep.char_one, scalar-product and Fourier
basis results; none gives the elementary induction identity. msearch.py loogle
`FDRep, "ind"` returned no hits. msearch.py grep
`Brauer|IsElementary|elementary.*subgroup` in RepresentationTheory returned no hits.

For the new elementary-group notion, msearch.py leansearch query “A finite elementary
group is a direct product of a cyclic group of order coprime to a prime p and a group
of p power order” returned 8 hits including IsPGroup.iff_card, IsPGroup.of_card and
cyclic-product coprimality. msearch.py leanfinder query “finite group elementary
direct product cyclic coprime p group” returned 8 hits about Z-groups and cyclic
products. These are different predicates: Z-groups require cyclic Sylow subgroups,
whereas an elementary group's p-factor can be any p-group. msearch.py grep
`IsElementary|Brauer|elementary.*(group|subgroup)` in GroupTheory returned no hits.
The exact returned search records are preserved in the new node's mathlib_searches.

Repository searches used rg on WeilConjectures and Sheaf for IsElementary,
IsBrauerElementary, elementary subgroups, and the item id. The only relevant hits
are references to this yet-unstated result in BrauerMonomialInduction; other
IsElementary names concern étale morphisms, contractions, or standard ring elements.
DAG filename and content searches found no definition node for elementary finite
groups; existing statement nodes repeat the inline definition. tools/blueprint_refs.py
search 'elementary subgroup' returned zero blueprint nodes. Its ancestor command
identified lem-per-artin-gabber-affine-curve. The latest blueprint Step 3 was read;
it does not prove this auxiliary representation-theory input. The new node retains
the accepted source's distinction between ILO motivation and the wanted Serre source.

No STATEMENT-DISPUTED issue or statement correction was found. This is not a unit's
own statement. No claim of having obtained or read the wanted Serre text is made.

Validation: both delivered modules compiled separately, in dependency order, with
scompile.py against the live server publication. All variables and universes are
explicit; autoImplicit is disabled. No theorem is proved in this stage-2 delivery.

## New nodes

`def-per-brauer-elementary-group` defines the exact elementary-group predicate
spelled out inline in the item's statement: a product of a cyclic prime-to-p group
and a p-power-order group, for some prime p. Its module is
Sheaf.GroupTheory.BrauerElementary and its declaration Group.IsBrauerElementary.
The factors are encoded as subgroups of the finite group, with a group isomorphism
from their external product, an equivalent formulation by taking factor images.
Its source is the accepted item's definition in the auxiliary ILO X 1.2 context,
with the same wanted Serre II Chapter 10 reference. The three real search kinds
above found no existing predicate; no DAG definition carries it. No proof-only
fact, new axiom, auxiliary postponed theorem, or hollow construction was added.

Dry-run schema repair: the live server preflight requires `import_flags` on a new
definition node, although the standing brief omits it. Added the empty list; no
mathematical statement, dependency, or proof was changed.

## Second reading by Q122

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
