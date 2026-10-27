## Worker report

The module `Sheaf.RingTheory.BasisConeGroupLocalization` states
`AddMonoidAlgebra.basisCone_group_localization`, with its proof postponed by `sorry`.
Five real helper definitions introduce the cone, its basis monomials, its denominator
submonoid, a specified denominator product, and the canonical algebra inclusion.
They introduce the local objects expressly defined in this node, rather than independent
notions. Every helper and the theorem is listed in `lean.declarations`. No definition
uses a postponed theorem or has missing data. There are no new nodes or dependency modules.
The node copy changes only `lean`; its accepted split and statement remain unchanged.

Hypotheses and clauses, matched individually:

- A field k is `{k : Type u} [Field k]`, using the Mathlib declaration of
  `def-weil-field`. The universes u and v are independent and explicitly declared.
- An additive abelian group G is `{G : Type v} [AddCommGroup G]`. Its integer
  module structure is the canonical one on any additive commutative group; it is
  not an additional hypothesis or a chosen scalar action.
- A finite integral basis is `{r : ℕ}` and `b : Module.Basis (Fin r) ℤ G`.
  `Basis.repr` is a linear equivalence with the finitely supported integer coordinate
  functions, hence encodes existence and uniqueness of precisely these coordinates.
- H is `basisCone b := AddSubmonoid.closure (Set.range b)`. This is exactly the
  natural-coordinate cone: Mathlib's additive version of
  `Submonoid.mem_closure_range_iff_of_fintype` identifies it with the sums
  `∑ i, a i • b i`, for `a : Fin r → ℕ`. There is no saturation or negative exponent
  in H. Its zero and addition closure are supplied by `AddSubmonoid` itself.
- Both k[H] and k[G] are Mathlib `AddMonoidAlgebra`, the finite-support coefficient
  functions with convolution multiplication. Their monomial is `single exponent 1`;
  multiplication adds exponents, as required by the node.
- C as a subalgebra is represented by its canonical injective algebra map
  `basisConeInclusion b := mapDomainAlgHom k k (basisCone b).subtype`.
  The first theorem conjunct states its injectivity, so this has exactly the same
  content as identifying C with its image in the group algebra.
- `basisConeVariable b i` is the single monomial at b i, whose membership in H is
  constructed using `AddSubmonoid.subset_closure`. `basisConeDenominators b` is the
  multiplicative closure of these monomials. The theorem's third conjunct explicitly
  identifies every element of this closure with a product parametrized by
  `a : Fin r → ℕ`, via `basisConeDenominator b a`. This is exactly the displayed S.
  Multiplicative closure and the empty product are built into the Submonoid; the
  second conjunct states `0 ∉ basisConeDenominators b`.
- S inverse C is `Localization (basisConeDenominators b)` and a/s is
  `Localization.mk a s`. Mathlib `Localization.mk_eq_mk_iff` and `r_iff_exists`
  give equality precisely when some denominator t satisfies t*(s'*a)=t*(s*a').
  Since C is a commutative ring this is equivalent to t*(a*s'-a'*s)=0, the
  fraction relation in the node, with no domain or regularity assumption added.
- The existential `θ : Localization ... ≃ₐ[k] AddMonoidAlgebra k G` is the asserted
  k-algebra isomorphism. The first clause under this existential says that its
  composite with `algebraMap C (Localization S)` is the canonical inclusion.
- The next clause quantifies over all k-algebra maps φ with that same composite
  and concludes `φ = θ.toAlgHom`, expressing uniqueness of the extension.
- The following clause gives θ on every fraction, as the inclusion of a times
  `Ring.inverse` of the inclusion of s. `Ring.inverse` is the inverse of a unit
  in an arbitrary ring, with default zero on nonunits; here all denominators are
  units, by their monomial form in the group algebra. No field structure is
  incorrectly imposed on k[G].
- The last clause quantifies over all `n : Fin r → ℤ` and gives θ.symm on
  `single (∑ i, n i • b i) 1` as the fraction with numerator product
  `basisConeDenominator b (fun i ↦ (n i).toNat)` and denominator product
  `basisConeDenominator b (fun i ↦ (-n i).toNat)`.
  Integer toNat is max(n,0) as a natural number. Thus these are precisely the
  positive and negative coordinate parts. The inverse of an algebra equivalence
  is both k-linear and a unital ring homomorphism, supplying both final clauses
  about the inverse. The basis spans the group algebra, so its values on these
  monomials determine the entire inverse.
- r=0 is permitted: `Fin 0` is empty. The basis forces G=0; closure of the empty
  family is the zero submonoid, both monoid algebras are the constants k, and
  the multiplicative closure of the empty monomial family is {1}. Every product
  in the statement is then the empty product. No positivity assumption on r occurs.

Dependency declarations read and used:

- `def-weil-field` has Mathlib match `Field`, in `Mathlib.Algebra.Field.Defs`.
  Read the complete Field signature and its DivisionRing/CommRing parents:
  nontriviality and inverses of nonzero elements are included.
- The proof dependency `lem-weil-pbc-ring-localization-universal-property` is a
  Mathlib leaf, matched to `IsLocalization.lift` and `IsLocalization.ringHom_ext`
  in `Mathlib.RingTheory.Localization.Defs`. Their complete signatures and
  docstrings, together with `lift_mk'`, `lift_eq`, and `lift_of_comp`, were read.
  `Mathlib.RingTheory.Localization.Basic` publicly imports this interface.
- Other definitions are the existing `Module.Basis`/`Basis.repr`,
  `AddMonoidAlgebra.mapDomainAlgHom`, `AddMonoidAlgebra.single`,
  `AddSubmonoid.closure`, `Submonoid.closure`, `Localization.mk`, and `Ring.inverse`.
  `Mathlib.Algebra.Group.Submonoid.Finsupp` is imported for the existing
  closure/finite-coordinate descriptions needed by the proof.

Source checks: read ILO VIII, Lemma 3.2.12, printed p.104 (PDF p.110).
It identifies k[P^gp] with the lattice group algebra k[Z^n]; the explicit
basis-cone localization calculation is correctly identified in the node and module
as the agent-written expansion. Read the current blueprint's
`sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md`:
this node is a historical algebraic input, not a replacement of that unit's
contracting-correspondence statement. No statement correction is needed.

Edge checks: rank zero and empty products as above; rank one gives k[x,x^-1];
coordinates (2,-3) give x1^2/x2^3; zero coordinates give exponent zero in both
products; arbitrary positive characteristic is allowed; the inverse formula
uses Ring.inverse rather than assuming the group algebra is a field. Arbitrary
independent coefficient and lattice universes are supported. No node fault or
STATEMENT-DISPUTED flag was found.

Searches, before adding declarations (the retained searches.jsonl records the calls):

- LeanFinder: “Localizing the monoid algebra of the nonnegative cone of an integral
  basis at its basis monomials gives the group algebra with inverse sending signed
  exponents to positive over negative monomials” returned eight hits on localized
  module bases, number-field integral bases and submersive presentations, none this
  algebra equivalence. A fresh search for “The group algebra of a free abelian group
  with a finite integral basis is the localization of its nonnegative cone monoid
  algebra at the basis monomials” returned eight number-field localization/integral
  basis hits; again none states this result.
- Loogle: `AddMonoidAlgebra, IsLocalization` returned zero hits (also repeated).
- msearch grep: `(MonoidAlgebra|AddMonoidAlgebra).*(localiz|IsLocalization)|localiz.*(MonoidAlgebra|AddMonoidAlgebra)`
  returned zero hits (also repeated).
- LeanSearch: “The group algebra of a finite rank free abelian group is the
  localization of the algebra of its positive basis cone” returned eight general
  localization and finite-type monoid-algebra results, none the requested theorem.
- Project rg in both `lean/WeilConjectures` and `lean/Sheaf` for
  `basisCone|basisCone_group_localization|basis.cone.*localiz|lem-trf-basis-cone-group-localization`
  returned no match. A broader search for
  `MonoidAlgebra.*[Ll]ocaliz|[Ll]ocaliz.*MonoidAlgebra|basis[Cc]one|basis_cone|lem-trf-basis-cone-group-localization`
  found only two unrelated uses of the formal-monoid model at a prime localization
  in `FormalMonoidExtensionModel.lean`, not this notion or statement.
- Read Mathlib's Basis, monoid-algebra mapDomainAlgHom, localization fraction
  relation and inverse definitions rather than introducing copies of them.

Validation: scompile.py compiled the module as a sandbox and at its intended
library name with no errors or unexpected warnings. The final packet is checked
again by deliver2.py, including the final added proof import. The inherited ending
was a stage-1 unchanged-split rejection: the current stage-2 handoff explicitly
permits giving an accepted split its Lean record, and coord/queue.tsv lists this
item at stage 2. There is no repair note for this item.

## Second reading by Q143

No independent second worker was started, as required by this dispatched brief.
The maintainer's independent review reads the delivery. The author's final check
reread the node against the file, matching each hypothesis and clause above.
The retained draft already had the correct mathematical signature and required
module conventions. The resumed audit reread the Field and localization dependency
signatures, the latest blueprint, and ILO printed p.104; repeated LeanFinder, Loogle,
Mathlib grep and project searches; and recompiled the unchanged module through
scompile.py in both sandbox and intended-library modes (each completed in 1.1 s).
The node copy was refreshed from the live accepted split, changing only lean. No mathematical statement was
changed, and the only postponed proof is the named theorem recorded by this node.
