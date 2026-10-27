## Worker report

The module `Sheaf.AlgebraicGeometry.GRingAlterationClosedFibreNeighbourhood` states
`AlgebraicGeometry.exists_gRing_alteration_closed_fibre_neighbourhood`. Its sole theorem
has proof `sorry`; no definitions, extra nodes, dependency repairs, or statement corrections
are introduced. Only the item's `lean` field changes.

Source checked online: Kurano--Shimomoto, *Ideal-adic completion of quasi-excellent rings
(after Gabber)*, https://www.isc.meiji.ac.jp/~kurano/ronbun/kurano40.pdf, Definition 3.2
(printed p. 3) and Lemma 4.4 with proof (printed pp. 5--6). The source assumes B_q is
a G-ring; the accepted node is the stated specialization with global G-ring B.
The proof uses localization of the G-ring condition, without universal catenarity.
The paper is not archived locally, as the existing node's source record already notes.

Clause-by-clause rendering:

- Commutative Noetherian integral domain B: `(B : Type u) [CommRing B] [IsDomain B]
  [IsNoetherianRing B]`. G-ring: `(hB : IsGRing B)`.
- Arbitrary ideal J and prime q: `(J q : Ideal B) [q.IsPrime]`.
- J-2 of B/J: `hJ` quantifies over all commutative finite-type `(B ⧸ J)`-algebras D
  and asserts `IsOpen {r : PrimeSpectrum D | IsRegularLocalRing
  (Localization.AtPrime r.asIdeal)}`. This is exactly the J-2 clause of the recorded
  `IsQuasiExcellent` definition, with neither a quotient G-ring nor catenarity assumed.
  D uses the universe of B: every finite-type algebra has a polynomial quotient model
  there; this is not a restriction on the mathematical algebras covered.
- Principal neighbourhood: `∃ b : B, b ∉ q ∧ ...`; the target everywhere is precisely
  `Spec (.of (Localization.Away b))`, with its canonical algebra map from B.
- Finite family: `∃ (n : ℕ) (X : Fin n → Scheme.{u}) (φ : ∀ i, X i ⟶ ...)`.
  Its integral and Noetherian clauses are `IsIntegral (X i) ∧ IsNoetherian (X i)`.
  Mathlib `IsNoetherian` means locally Noetherian and compact, equivalently a finite
  affine cover by Noetherian rings, matching the node.
- Dominance: `DenseRange (φ i)`. Finite type: `LocallyOfFiniteType (φ i) ∧
  QuasiCompact (φ i)`, the recorded Mathlib rendering of finite type.
- Generic finiteness: `∃ η : X i, IsGenericPoint η Set.univ ∧
  ((φ i).stalkMap η).hom.Finite`. On integral schemes a generic point exists and is
  unique. Continuity and dense image imply its image is the target's generic point:
  the closure of the image point contains the whole image and hence the whole target.
  Therefore this stalk map is exactly k(Y) → k(X_i), with the function fields defined
  as generic stalks in the node. `RingHom.Finite` means the target is a finite module
  via that very map. There is no arbitrary field inclusion or algebra structure.
  This avoids choosing or transporting generic-point equalities in the signature.
- Closed-fibre membership: `Ideal.map (algebraMap B (Localization.Away b)) J ≤
  (φ i x).asIdeal` says exactly that the image prime contains JB[1/b].
- Regularity there: `IsRegularLocalRing ((X i).presheaf.stalk x)`, the local ring
  of the ambient X_i; it is not the stalk of a closed subscheme or quotient.
- Witness: `∃ (V : Scheme.{u}) (p : V ⟶ ...)`, with `IsIntegral V ∧ IsNoetherian V
  ∧ IsProper p ∧ Surjective p`. Its generic finiteness is expressed by the same
  canonical generic stalk map; surjectivity implies dominance. Properness includes
  the witness's finite-type condition.
- Finite indexed open cover: `∃ (U : Fin n → V.Opens) ...`, with `(⨆ i, U i) = ⊤`.
- Y-morphisms: `h : ∀ i, (U i).toScheme ⟶ X i` and the exact equations
  `h i ≫ φ i = (U i).ι ≫ p`. The same index type is used for the members and opens.
- No excellence of B_q, universal catenarity of B, degree restriction, separability,
  invertibility hypothesis, or regularity of the whole X_i has been added.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `WeilConjectures.RingTheory.GRing`: `IsGRing`, with its canonical completion maps.
- `Sheaf.RingTheory.ExcellentRing`: the J-2 clause of `IsQuasiExcellent`, expanded
  directly rather than copying or strengthening the full quasi-excellence predicate.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Scheme.Hom.stalkMap`.
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`; its ring
  structure and canonical map come from `Mathlib.RingTheory.Localization.Away.Basic`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, with
  `QuasiCompact` from `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: recorded scheme definition and
  `Mathlib.RingTheory.RegularLocalRing.Defs.IsRegularLocalRing` for its ring clause.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`.
- `Mathlib.Topology.Sober`: `IsGenericPoint`, the closure-of-a-singleton definition.

Every recorded statement-dependency module is publicly imported (some through the public
imports above). Stated proof dependencies have ordinary imports: finite presentation,
quasi-separatedness, localization finiteness, iterated localization, constructibility,
and `WeilConjectures.Topology.ProconstructibleClosureSpecialization`.
The proof-only nodes `lem-per-j2-closed-fibre-regular-locus`,
`lem-per-local-alteration-diagram-spreading`, `lem-per-qe-weak-uniformization-cover`, and
`lem-per-semilocal-g-ring-j2` currently have no recorded Lean declaration; no import is
invented for them. They are not needed to type the statement. All eight proof steps,
including their named DAG inputs, are in the theorem docstring for stage 3.

Edge cases checked before writing:

- J = 0 requires ambient regularity everywhere, as V(0) is the whole target.
- J = B gives an empty closed fibre and makes exactly the regularity clause vacuous;
  all alteration-cover data remain required. The zero quotient is allowed in hJ.
- q need not contain J; the statement does not require it.
- q = 0 and B a field are admitted. In all cases b ∉ q forces b nonzero and gives
  a nonempty integral principal neighbourhood.
- n = 0 is syntactically allowed but cannot witness the conclusion: an integral V
  is nonempty, while its empty supremum of opens is bottom and cannot cover it.
  No unnecessary positive-size hypothesis is introduced.
- Individual U_i can be empty. Each X_i and V is nonempty because it is integral.
- Arbitrary characteristic and inseparable generic extensions are allowed.
- The zero ring cannot be B because IsDomain includes nontriviality, exactly as
  integral domain does. B/J may be nonreduced; no reducedness assumption is made.

Searches performed with the prescribed msearch wrapper and local source searches:

1. LeanFinder: "A Noetherian G-ring with J-2 quotient admits alteration covers regular
   above the closed fibre on a principal neighbourhood of each prime". Eight hits,
   including `Algebra.QuasiFiniteAt`, smooth loci, and `IsLocallyNoetherian`; no match.
2. Loogle: "IsGRing, IsRegularLocalRing". Zero hits; IsGRing is unknown to the service.
3. Mathlib grep: `GenericallyFinite|genericallyFinite|alteration|IsJ2Ring`. Zero hits.
4. LeanSearch: "Alteration covering of a G-ring on a principal neighbourhood with
   regular ambient local rings above a J-2 quotient". Eight hits about Jacobson rings,
   affine covers, and local properties of quasi-finite maps; no match.
5. Local rg in `lean/WeilConjectures` and `lean/Sheaf` for the item id, alteration,
   generic finiteness, G-rings, J-2, and the proposed theorem name. Found the recorded
   definitions and unrelated alteration theorems, not this statement. Upstream
   `RingTheory.Excellent.IsJ2` is an equivalent definition but importing that module
   together with the recorded dependency would import duplicate catenary definitions;
   the statement instead expands the J-2 clause of the recorded dependency itself.
6. Searched Mathlib for function fields, generic-point maps, stalk maps, dominance,
   generic points and finite ring homomorphisms. Reused `stalkMap` and `RingHom.Finite`;
   no helper or second notion was introduced. A named projectivity result on zero-
   dimensional generic fibres is a different theorem with different hypotheses.

Validation: scompile.py compiled the file both as a sandbox module (2.1 s) and as its
library module (1.7 s), with no errors or unexpected warnings.
No STATEMENT-DISPUTED flag or node fault was found.

## Second reading by Q108

I reread the node alongside the final file after compilation, separately from drafting;
this is a worker self-check, with the maintainer's independent review still to follow.
The binders include exactly the Noetherian domain, G-ring, ideal, prime, and quotient J-2
hypotheses. The conclusions retain the same principal target, integral Noetherian family,
dominance, finite type, generic finiteness, ambient closed-fibre regularity, and integral
Noetherian proper surjective generically finite witness. The cover and the family share
Fin n, and the commuting equation has the correct direction for a morphism over Y.
I specifically checked that finiteness is on the induced generic stalk map, not a free
field embedding, and that no quotient stalk replaces the ambient stalk. The existential
choice of a generic point changes no object: it is unique on an integral scheme.
No mismatch was found and no statement change was made.
