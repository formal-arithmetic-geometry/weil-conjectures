## Worker report

Item: `lem-sfb-trivial-ladic-derived-exterior`.
Module: `Sheaf.Paper.TrivialLadicDerivedExterior`.
Main declaration: `Profinite.TrivialLadicExterior.trivial_ladic_derived_exterior`.

The module constructs the specified coordinate-cup arrow, then states that this arrow
is an isomorphism for each of the two coefficient fields. It also states the rank-zero
identity with canonical source identification and a target identification normalized by
the actual invariant unit. The natural-language statement is unchanged. The return
repair adds a lattice definition node and repairs the polynomial comparison module to retain its old lattice name as an
alias. All twelve item declarations are recorded in `lean.declarations`.
The helpers belong to constructions explicitly requested in this node, rather than
introducing a separate cohomology, coefficient ring, action, or cup product.

Hypothesis and clause correspondence:

| Node | Lean rendering |
| --- | --- |
| Prime ell | `(ell : ℕ) [Fact ell.Prime]` |
| Algebraic closure Omega of Q_ell | `(Ω : Type u) [NormedField Ω] [NormedAlgebra ℚ_[ell] Ω] [IsAlgClosure ℚ_[ell] Ω]` |
| Extended norm topology | The topology is the one supplied by `NormedField Ω`, compatible with the p-adic norm by `NormedAlgebra`; no separate topology instance is supplied. |
| Finite intermediate extension E/Q_ell | `(E : IntermediateField ℚ_[ell] Ω) [FiniteDimensional ℚ_[ell] E]`; its norm and topology are inherited from Omega. |
| Both F=E and F=Omega | The main conclusion is the conjunction `IsIso (exteriorMap ell E r) ∧ IsIso (exteriorMap ell Ω r)`. |
| A_F(S)=C(S,F), all continuous maps | `continuousScalarRing F`, whose fields are exactly `continuousMapRingObjOfUniverse`, its canonical `MonObj`, and its commutativity witness. The universe lift changes no sections. |
| r at least zero, including zero | `(r : ℕ)` |
| L=Z_ell^r, inverse-limit/product topology | The definition-node-owned `Profinite.LadicLattice.Lattice.{u} ell r = Multiplicative (ULift.{u} (Fin r → ℤ_[ell]))`; the two wrappers only change universe and group notation. The p-adic integers have their standard p-adic topology. |
| Trivial condensed action on the coefficient | `cohomology A L` uses `coefficient A L`, the single complex on `trivial.obj (Mod.regular A.X)`. No representation is supplied as an extra hypothesis. |
| Ordinary internal-module derived invariants | `CondensedDerivedRestriction.cohomology A L = (derived A L).obj (coefficient A L)` in `DerivedCategory.{u+1} (Modules A)`, where `Modules A` is the recorded category of internal module objects. |
| The ith coordinate inclusion into F | `coordinateSection ell F r i S g = ULift.up ⟨fun s ↦ algebraMap ℚ_[ell] F ((g s).toAdd.down i : ℚ_[ell]), ...⟩`. Indices `Fin r` correspond to paper indices 1,...,r in their increasing order. |
| Additive condensed character, on all test objects | `coordinateSection_laws` states identity, addition, and naturality under every `f : T ⟶ S`. `coordinateCharacter` uses precisely these laws and the displayed section function. |
| Alpha_i is the connecting character class | `characterClass (coordinateCharacter ell F r i)` uses the recorded positive unipotent extension construction; no arbitrary degree-one class is introduced. |
| Zero-differential exterior complex, term a sum on q-subsets | `exteriorObject r A := ⨁ fun I : Finset (Fin r) ↦ shiftedRegular A I.card`, with `shiftedRegular A n := (singleFunctor ... 0).obj (Mod.regular A.X)⟦-(n:ℤ)⟧`. This is exactly the node's explicitly equivalent finite sum of shifted single complexes. Every summand has zero differential and lies in its indicated degree; no summand exists in negative degree or above r. |
| Canonical identification A[-q] with the tensor of q degree-one sources | `splitShift A n` uses only the integer shift equality, derived tensor-shift iso, regular-unit iso, and left unitor. It fixes a right-associated tensor convention without selecting a comparison map. |
| Increasing ordered product on I={i1<...<iq} | `subsetCup` applies `orderedCoordinateCup` to `I.sort (· ≤ ·)`, casting along `Finset.length_sort`. The recursive definition tensors the first actual character class with the remaining product, then applies the recorded `cup`. No permutation occurs. |
| Empty-subset component is the unit | The empty-list branch uses `shiftFunctorZero`, `baseUnitIso.inv`, then the recorded `cupUnit`. |
| The specified map chi | `exteriorMap := biproduct.desc (subsetCup ell F r)`. Thus the components determine the arrow by the coproduct universal property; it is not an arbitrary morphism assumed to have the needed properties. |
| This morphism is an isomorphism in D(Mod_A) | The main theorem applies `IsIso` to the constructed `exteriorMap`, separately for E and Omega. The conclusion is about the arrow in the derived category, not just its homology or existence of some unrelated iso. |
| Rank zero is the identity A[0] | `rankZeroSourceIso A` is the canonical unique-index biproduct iso followed by the zero-shift iso. `rankZeroNormalization` gives `e : C_A(L_0) ≅ A[0]`, requires `(baseUnitIso.inv ≫ cupUnit) ≫ e.hom = 𝟙 _`, and states `exteriorMap ell F 0 ≫ e.hom = rankZeroSourceIso.hom`. Hence the normalized map is exactly the identity. The first equality uniquely pins the target iso by its canonical invariant unit. This helper applies to both E and Omega without a completeness hypothesis. |
| No completion or finite-subextension-union topology | Every coefficient section is an actual continuous map to the given normed field. There is no `CompleteSpace`, completed field, locally constant condition, or colimit over intermediate fields. |

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `ModObj`, `Mod.regular`.
- `Sheaf.CategoryTheory.CondensedActionModule`: `Profinite.CondensedAction.Modules`,
  `ActionModule`, `trivial`, and its sectionwise action convention, through the recorded
  `CondensedBar.Modules`, `Equivariant`, and trivial coefficient.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and the standard localization conventions. Single complexes
  and shifts are the existing derived-category constructions.
- `Sheaf.Topology.ContinuousMapCondensedRing`:
  `Profinite.continuousMapRingSheafOfUniverse`, `continuousMapRingObjOfUniverse`,
  `continuousMapRingObjOfUniverseMonObj`, and its commutativity witness, through the
  recorded `continuousScalarRing` bundle.
- `Sheaf.CategoryTheory.ContinuousScalarRing`:
  `Profinite.CondensedAction.continuousScalarRing`.
- `Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus` and its public dependencies:
  `CategoryTheory.CondensedDerivedRestriction.cohomology`, `cup`, `cupUnit`,
  `baseUnitIso`, `Character`, `characterClass`. The latter's full source was read:
  it is the positive connecting class of the actual unipotent extension, shifted down
  by one. The module's cup is the normalized derived lax multiplication, not
  topological continuous cohomology.
- `Sheaf.Topology.LadicLattice`: `Profinite.LadicLattice.Lattice` and its
  `latticeTotallyDisconnected`, owned by the new `def-sfb-ladic-lattice`.
- `Sheaf.CategoryTheory.PolynomialDerivedBarComparison`: retained solely as a
  non-public proof import. Its compatibility alias `PolynomialBar.Lattice` now
  reduces to the new owned definition; the comparison theorem is unchanged.
- `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift`:
  `DerivedCategory.shiftTensorShiftIso`, used directly to build `splitShift`.

The item directly cites the already-landed `def-sfb-bundled-continuous-scalar-ring`,
`def-sfb-condensed-derived-cup`, and `def-sfb-condensed-unipotent-class`, plus the new
`def-sfb-ladic-lattice`. The added theorem statement dependency from the returned
packet has been removed; no original statement dependency is removed. Cup and
positive connecting characters still use precisely the same recorded definitions.

Polynomial derived-bar comparison, rational polynomial contraction and derived
invariant bar remain non-public proof imports. The polynomial theorem's conclusion
is not used to type any item declaration. `lem-sfb-internal-bar-ordered-cup` has no
recorded module in the source read; its exact role remains in the proof docstring.
The proof docstring includes every step of the node's six-step argument, including the sign automorphism
and the absence of a columnwise acyclicity or completion claim.

Edge cases checked by reading the actual definitions:

- `r=0`: `Fin 0` is empty, `Finset (Fin 0)` has one element, and the lattice is the
  one-element group. The source is the unique empty summand; the separate normalized
  equality explicitly retains the identity clause.
- Empty subset for every r: sorting gives the empty list and recursion gives the
  actual cup unit. No nonempty-index restriction appears.
- Singletons: their sorted list has one coordinate and recursion gives that
  character class cupped with the unit, hence that class by the existing unit law.
- q greater than r or negative: there is no such subset summand; all shifted regular
  summands occur in degrees 0 through r, with zero differential.
- The full subset has its increasing order, so no hidden choice of orientation or
  permutation can change the specified map.
- All primes, including ell=2, are retained. No division by ell, odd-prime hypothesis,
  or characteristic shortcut was added.
- The finite-extension identity case `E=⊥` is allowed. No properness of E is required.
- Noncomplete Omega and continuous maps whose images are not in one finite extension
  are retained: neither completeness nor a finite-image condition appears.
- `u` is explicit, `autoImplicit` is false, the small profinite parameters and field
  are taken in their common containing universe, with coefficients and derived Hom
  in `u+1`, exactly as in the recorded dependencies.

Searches for existing declarations (all prescribed search kinds were run):

- `msearch.py ... leanfinder`: "Derived condensed invariants of Zp power r with trivial
  p adic coefficients are the exterior complex of coordinate cup products".
  Result: eight hits, including `BDeRhamPlus`, `BDeRham`,
  `Condensed.profiniteFree`, `Condensed.profiniteSolid`, and
  `ContinuousCohomology.MultiInd.complex`; none is the specified internal derived map.
- `msearch.py ... leansearch`: "Derived invariants of p adic integers with trivial
  continuous field coefficients are an exterior algebra on coordinate characters".
  Result: eight p-adic/Mahler hits, including `PadicInt.mahlerTerm`,
  `PadicInt.isFractionRing`, and `PadicInt.continuousAddCharEquiv_apply`; no match.
- `msearch.py ... loogle`: `"singleFunctor", "shift"`.
  Result: twelve `CategoryTheory.SingleFunctors.shiftIso` and compatibility hits.
  These are general shift APIs, not this exterior calculation.
- `msearch.py ... grep`: `(exterior|cup|koszul).*(cohomology|invariant)|(cohomology|invariant).*(exterior|cup|koszul)`
  in `RepresentationTheory`. Result: zero hits.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  searched the item id, trivial-ladic names, coordinate characters, ordered cup products,
  exterior complexes, and expected full declaration names. The only prior citation of
  this item is a proof-plan comment in `DenseLatticeDerivedInvariants.lean`; no theorem
  or specified exterior map exists. The rational polynomial contraction defines its
  own algebraic exterior complex for ordinary modules, not the present condensed
  internal-module arrow. Existing cup, positive character, continuous coefficient,
  lattice and tensor-shift APIs were found and reused. The lattice expression is now
  owned by the new definition node, with the previous helper retained as an alias.

No statement correction or mathematical counterexample was found. The node's source
itself labels the exact all-continuous noncomplete-coefficient analytic reference WANTED;
this delivery preserves that obligation and does not claim to prove it. Every postponed
proof is `sorry`: `coordinateSection_laws`, `trivial_ladic_derived_exterior`, and
`rankZeroNormalization`. Every definition has real construction data. The coordinate
laws are a named theorem about the explicit coordinate formula, and are the only
postponed proof needed to build the corresponding `Character` record.

## New nodes

`def-sfb-ladic-lattice` owns `Sheaf.Topology.LadicLattice` and
`Profinite.LadicLattice.Lattice`. Its definition is exactly the former lattice
expression, `Multiplicative (ULift.{u} (Fin r → ℤ_[ell]))`. The prime binder,
nonnegative rank, coordinatewise additive law, standard product topology, containing
universe lift, and notation-only multiplicative tag render each clause of the new
node. The instance `latticeTotallyDisconnected` transports the existing product
instance by `Homeomorph.ulift.symm`. It has no postponed proof or data. `r=0` gives
a unique function from the empty type, hence the one-element group. Arbitrary rank
and ell=2 are included. No topology or algebraic structure is assumed externally.

The source is the item's main-20261015 direct-images proof paragraph (3),
trivial-representation lattice base case; the current blueprint paragraph and the
item's agent-formulated descendant statement were both read. This definition
extracts the lattice already explicitly present there; it adds no analytic claim.
`def-weil-l-adic-numbers` supplies the p-adic integers via its Mathlib match
`PadicInt` in `Mathlib.NumberTheory.Padics.PadicIntegers`, whose definition and
norm-subtype docstring were read. The new node cites it. Its blueprint ancestor is
`null`, exactly the result of `tools/blueprint_refs.py ancestor` on this item; the
via list is the item's via list with the item prepended.

Ownership searches, recorded verbatim in `mathlib_searches`:

- `leansearch`: "The ell adic lattice Z ell power r with its product topology and
  additive group structure"; eight general group/adic-topology hits, no lattice.
- `leanfinder`: "Finite product of p adic integers is a compact totally disconnected
  topological additive group"; eight hits including `PadicInt`,
  `PadicInt.compactSpace`, and `PadicInt.completeSpace`, which give the factors and
  standard instances, not the finite-product declaration.
- `grep` in Mathlib NumberTheory/Padics:
  `abbrev.*Lattice|def.*Lattice|TotallyDisconnectedSpace.*PadicInt|PadicInt.*TotallyDisconnectedSpace`;
  zero hits.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf` and the upstream-name index for
  lattice declarations and both proposed full names: only `PolynomialBar.Lattice`
  has this exact expression; all other lattice notions concern different objects.
- Read all DAG definition statements mentioning p-adic integers or Z_ell, searched
  `dag/nodes`, and ran `tools/blueprint_refs.py search lattice`: no definition node
  owns the finite-rank topological group. The existing p-adic integer node owns its
  factors, and the polynomial theorem previously owned the unseparated helper.

There is one construction: the old helper is replaced by an alias, not duplicated.

## Dependency modules

`lem-sfb-polynomial-derived-bar-comparison`, module
`Sheaf.CategoryTheory.PolynomialDerivedBarComparison`, receives precisely the
§1(B) repair requested by the independent return. Its old module was unusable as a
statement-level owner of the lattice: the item needs the group and topology, not
that theorem's analytic conclusion. The module now publicly imports
`Sheaf.Topology.LadicLattice`; its `PolynomialBar.Lattice` abbreviation is
`Profinite.LadicLattice.Lattice.{u} ell r`, and its old disconnectedness instance
uses the owner's instance. Every other declaration, formula, binder, comparison
property, and proof docstring remains byte-identical. In particular the old and new
lattices reduce to the same expression, so polynomial evaluation and all existing
consumers retain their types by definitional equality. The dependency JSON changes
only `lean`, with the reason recorded in `lean.note`. The node's statement,
statement dependencies, proof and proof dependencies remain unchanged.

## Return repair

Return L/H2 at immutable head `130eb8bf28ea` asked for definition-node ownership of
the lattice and a compatibility alias. Both are implemented as above. The item
imports and opens the new owner directly and cites `def-sfb-ladic-lattice` in
`stmt_deps`, replacing the returned packet's added theorem dependency. The theorem
module remains a non-public proof import, as required by the stage-2 proof plan.
The advisory is also implemented: both `def-sfb-condensed-derived-cup` and
`def-sfb-condensed-unipotent-class` are direct statement dependencies and public
imports. No mathematical statement correction is needed. Comparing the packet
with the current live source shows the only original-node field changes are
`lean` and the item's permitted statement-dependency additions; this is a concrete
repair, not an unchanged re-push or rebase.

Validation: the saved packet first passed `deliver2.py --no-push` at
`06421e575b8`. The repaired three modules then compiled separately with
`scompile.py`: the actual module-path passes took 3.5 seconds for the lattice,
8.4 seconds for the polynomial comparison compatibility repair, and 49.3 seconds
for the item. No errors or non-sorry warnings remained. The repaired packet passed
`deliver2.py --no-push` at `e7f44f9752b`, including the server preflight and all
per-file compiles. Delivery uses the same prescribed wrapper.

## Second reading by O3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
