## Worker report

Item: `lem-trf-henselization-tensor-local-comparison`.
Module: `Sheaf.RingTheory.HenselizationTensorLocalComparison`.
Main declaration: `Algebra.henselization_tensor_local_comparison`.
Only `lean` changes in the node. No statement correction, new nodes, or dependency repairs.
The theorem has one `sorry`. Its docstring gives the node's eight-step proof, including
all proof dependencies. No theorem is proved in this delivery.

The auxiliary `RingHom.pointedKernelLocalization ε` transparently abbreviates
`Localization.AtPrime (RingHom.ker ε)` with the existing proof
`RingHom.ker_isPrime ε` supplied explicitly. It is a convenience for expressing the
canonical localization at an existentially bound evaluation map; it does not introduce
a different localization, an arbitrary ring, or an assumed prime ideal. All its data
is Mathlib's construction. It is recorded in `lean.declarations` with the main theorem.

Hypotheses, in order:

- Commutative rings A and B and their homomorphism: `(A : Type u) (B : Type v)`
  with `[CommRing A] [CommRing B] [Algebra A B]`. The map is `algebraMap A B`;
  every commutative-ring homomorphism determines such an algebra structure.
- Prime q of B with inverse image p: `(p : Ideal A) [p.IsPrime] (q : Ideal B)
  [q.IsPrime] [q.LiesOver p]`. `Ideal.LiesOver.over` is exactly
  `p = q.comap (algebraMap A B)`.
- R is an ordinary henselization of A_p: `(R : Type w) [CommRing R]`,
  `[Algebra (Localization.AtPrime p) R] [HenselianLocalRing R]`, and
  `hR : IsHenselizationAtPrime' A p R` use the recorded universal-property predicate.
- `[Algebra A R] [IsScalarTower A (Localization.AtPrime p) R]` express the
  restriction of the preceding structural map along A -> A_p. These are structural
  encodings, not an extra property of A -> B: every given A_p-algebra has this
  canonical restricted algebra structure. The scalar tower forces the restricted map.
- H is an ordinary henselization of B_q: `(H : Type z) [CommRing H]`,
  `[Algebra (Localization.AtPrime q) H] [HenselianLocalRing H]`, and
  `hH : IsHenselizationAtPrime' B q H`.
- `[Algebra (Localization.AtPrime p) (Localization.AtPrime q)]` together with
  `[Localization.AtPrime.IsLiesOverAlgebra p q]` encodes precisely the canonical
  local map of localizations. The latter's `algebraMap_eq` forces it to equal
  `Localization.localRingHom p q (algebraMap A B) Ideal.LiesOver.over`.
  Both structures are supplied canonically by `Localization.AtPrime.algebraOfLiesOver`;
  this adds no assumption on the map. This is also the interface used in the landed
  quasi-finite sibling.
- A, B, R, and H have independent universes u, v, w, z. No equality of universes,
  finite-type, quasi-finiteness, injectivity, Noetherianity, or separability is assumed.

Clauses, in the order of the node:

1. The structural residue isomorphisms are the output ring equivalences
   `iR : p.ResidueField ≃+* IsLocalRing.ResidueField R` and
   `iH : q.ResidueField ≃+* IsLocalRing.ResidueField H`.
   The first two conjuncts give their values on every element of A_p and B_q,
   respectively: `iR (residue A_p a) = residue R (algebraMap A_p R a)`, and the
   analogous equation for H. Thus they are the structural maps, not unspecified
   isomorphisms of abstract fields.
2. The canonical local map h is an output `h : R →+* H`, with `IsLocalHom h`,
   the equality of its composite with A_p -> R and A_p -> B_q -> H, and the
   uniqueness assertion for every other local map `h'` with that equality.
   This supplies the precise universal-property map used in the compatibility clause.
3. C is literally `R ⊗[A] B`; the output ring homomorphism `ε` has this domain.
   Its pure-tensor formula is exactly
   `Ideal.ResidueField.map p q (algebraMap A B) Ideal.LiesOver.over
   (iR.symm (IsLocalRing.residue R r)) * algebraMap B q.ResidueField b`.
   This is the node's R -> kappa(p) -> kappa(q), multiplied by the B residue.
4. n is exactly `RingHom.ker ε`; `(RingHom.ker ε).IsPrime` is explicitly concluded.
   D is exactly `RingHom.pointedKernelLocalization ε`, hence C_n.
5. The two `Ideal.comap` equalities assert that n contracts to `maximalIdeal R`
   under `TensorProduct.includeLeftRingHom` and to q under
   `TensorProduct.includeRight.toRingHom`. They concern the specified factor maps.
6. The output `iD : IsLocalRing.ResidueField D ≃+* q.ResidueField`, with
   `iD (residue D (algebraMap C D c)) = ε c` for every c, gives the canonical
   residue field of D. An equiv includes both injectivity and surjectivity.
7. The output `bD : Localization.AtPrime q →+* D` is characterized on B by
   `bD (algebraMap B B_q b) = algebraMap C D (1 ⊗ₜ[A] b)`.
   It is the canonical extension of B -> D to B_q, not an additional input map.
8. `RingHom.IndEtaleAcrossUniverses (bD.comp (algebraMap B B_q))` is B -> D
   ind-etale. The next conjunct applies the same recorded predicate to
   `(algebraMap B_q H).comp (algebraMap B B_q)`, giving B -> H ind-etale.
   This uses the recorded canonical ULift transport rather than imposing equal universes.
9. T is literally `R ⊗[Localization.AtPrime p] Localization.AtPrime q`.
   The output `εT` has the analogous pure-tensor formula, replacing the B residue by
   `IsLocalRing.residue B_q b`. n_T is exactly `RingHom.ker εT`, also explicitly prime.
10. The output `α : D ≃+* RingHom.pointedKernelLocalization εT` is the claimed
    D -> T_(n_T) equivalence. The two equations immediately before the conditional
    state that it sends the localized R factor to the localized R factor and
    `bD b` to the localized B_q factor. These determine the canonical tensor-factor
    comparison; they do not assert existence of an unrelated ring isomorphism.
11. Only inside `HenselianLocalRing D → ...` is the output `e : D ≃+* H`
    asserted. It is local by `IsLocalHom e.toRingHom`. Its B-factor equation says
    it is a B-algebra isomorphism without requiring a second independently chosen
    B-algebra structure on D. Its residue equation, for every d, is
    `iH.symm (residue H (e d)) = iD (residue D d)`, precisely identity on kappa(q).
12. The `∀ e'` conjunct proves uniqueness among ALL local ring equivalences
    satisfying only the B-compatibility and the prescribed residue identity.
    R-compatibility is not smuggled into the uniqueness predicate.
13. `∀ r, e (algebraMap C D (r ⊗ₜ[A] 1)) = h r` is exactly compatibility with h.
14. The last two conjuncts identify `(e.symm.trans α) : H ≃+* T_(n_T)` on
    `h r` and `algebraMap B_q H b`, respectively. Thus the final composite has
    both requested compatibilities, including the full B_q factor, not just B.

Canonicity of the output maps is expressed by their structural characterizations.
The quotient map of A_p or B_q is surjective, so the structural residue equations
uniquely specify iR and iH. Pure tensors generate C and T, so their displayed
formulas determine ε and εT. The fraction universal property specifies bD, and
specifies α from the two factor equations. iD is likewise determined after passing
to fractions. The local h and residue-compatible B-isomorphism e have explicit
uniqueness clauses. No canonical map is replaced by an arbitrary hypothesis.

Dependency declarations read and used:

- `Sheaf.RingTheory.GeneralizedHenselizationAtPrime`:
  `Algebra.IsHenselizationAtPrime'` (the node's recorded declaration).
- `Mathlib.RingTheory.Localization.AtPrime.Basic`:
  `Localization.AtPrime`, `Localization.localRingHom`,
  `Localization.AtPrime.algebraOfLiesOver`, and `Localization.AtPrime.IsLiesOverAlgebra`.
- `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`:
  `Ideal.ResidueField` and `Ideal.ResidueField.map`; its Basic dependency supplies
  `IsLocalRing.ResidueField`, `IsLocalRing.residue`, and the induced residue maps.
- `Sheaf.RingTheory.IndEtaleUniverseTransport`:
  `RingHom.IndEtaleAcrossUniverses`. It uses the existing ind-etale predicate on
  the canonical common-universe ULift of the specified ring map.
- `WeilConjectures.Mathlib.RingTheory.Henselian`:
  the recorded henselian terminology interface, including Mathlib's
  `HenselianLocalRing` (local root lifting, equivalent to the node's pair condition).
- `Mathlib.RingTheory.TensorProduct.Basic`:
  `Algebra.TensorProduct.includeLeftRingHom`, `Algebra.TensorProduct.includeRight`,
  and tensor products and pure tensors themselves.
- Proof-only imports: `Sheaf.TraceFormula.HenselizationPrimeIndEtale`
  (`RingHom.henselization_prime_indEtale`);
  `Sheaf.RingTheory.IndEtaleStability`
  (`RingHom.indEtale_principalZariski_stability`);
  `Mathlib.RingTheory.Etale.Basic` (`Algebra.Etale.finitePresentation`,
  `Algebra.Etale.of_isLocalizationAway`, and the localization instance);
  `WeilConjectures.RingTheory.MapIntoHenselianColimit`
  (`Algebra.map_into_henselian_colimit`). These are the four recorded proof tools.
  Their full theorem signatures and proof docstrings were inspected. The prime
  ind-etale tool's same-universe interface is a proof-stage transport issue, not
  an added restriction on this statement.

Source and edge cases checked before writing:

- Read Stacks `algebra.tex`, Tag 05WP statement and proof around lines 43581--43615.
  The node deliberately abstracts the pointed comparison in that proof, replacing
  the quasi-finite argument establishing henselianity by the conditional assumption
  on D. The conclusion about finiteness of R -> H from 05WP is not in this node.
- Read the current `literature/blueprint/latest` local-term-locality files. Their
  current contracting-correspondence argument agrees with the split report's
  observation that this ring tool is in the inherited auxiliary chain, not a current
  unit statement. No blueprint or unit change is proposed.
- Identity A -> A, equal primes: C is R and D is R; all structural identifications
  give the henselization identity. For a field extension k -> L at zero primes,
  R=k and H=L are the henselizations and the comparisons reduce to L.
- k -> k[x] at (x): D is k[x]_(x), generally not henselian. Ind-etaleness over B
  and α are asserted without henselianity; the comparison e is conditional, as needed.
- Quotient maps and noninjective A -> B are allowed: no injectivity occurs among
  the inputs. Both tensor evaluations remain well defined by their common A-action.
- If A or B is the zero ring, the required prime ideal cannot be supplied; no
  artificial nontriviality input is added. Zero tensor pathology is ruled out by
  the actual residue evaluation to a nonzero field, rather than an extra hypothesis.
- No characteristic condition and no finiteness conditions occur. All four ring
  universes are explicitly independent. `set_option autoImplicit false` verifies
  that no variables or universes are silently bound.

Searches (all run on 2026-10-24):

- `msearch.py ... leanfinder` query: "A henselian localization of the tensor base
  change of an ordinary henselization is canonically the henselization of the target
  local ring". Eight hits, led by `IsLocalization.tensorProduct_tensorProduct` and
  `IsLocalization.algebraTensorEquiv`, with localization/base-change lemmas. None
  states the pointed henselization comparison and all its clauses.
- `msearch.py ... loogle` query: `HenselianLocalRing, IsLocalization.AtPrime`.
  Zero hits.
- `msearch.py ... grep` query:
  `(henselization|henselisation).*(tensor|local)|(tensor|local).*(henselization|henselisation)`.
  Zero Mathlib hits.
- `msearch.py ... leansearch` query: "A henselian localization of the tensor product
  of an ordinary henselization with a ring is the target henselization and has its
  residue field". Eight hits: tensor-product localization, `HenselianLocalRing`,
  `HenselianLocalRing.TFAE`, localized-module facts; no complete match.
- `rg -n` for the same henselization/tensor/localization pattern in both
  `lean/WeilConjectures` and `lean/Sheaf` found related henselization tools,
  including `HenselizationQuasiFiniteRing`, which assumes finite type and
  quasi-finiteness and asserts finiteness. Its full declaration was read; it is
  not the present general conditional comparison. The strict-henselization tensor
  results also concern different objects.
- `grep -rn 'lem-trf-henselization-tensor-local-comparison' lean/WeilConjectures`
  found no declaration. Searches for both new full declaration names in Mathlib,
  `WeilConjectures`, `Sheaf`, and `dag/lean_names_upstream.json` found no collision.

No `STATEMENT-DISPUTED` issue was found. The definition dependencies are usable,
and the node is represented without changing its statement or dependency lists.

Validation: `scompile.py Q62 lem-trf-henselization-tensor-local-comparison` on the
module passed in both sandbox and library module modes (9.3 s and 6.1 s), with no
warnings or errors. A later direct public import of the recorded localization
module is also validated by the final delivery dry run. The JSON is indent 1,
UTF-8, with a final newline; its signature is extracted verbatim from the Lean file.

## Second reading by Q62

Fresh second pass by the same dispatcher-started worker: this is not an independent
second agent's review, since the assignment explicitly prohibits starting agents.
The maintainer's independent review is still required. I reopened the node and
checked the Lean against its complete statement, rather than treating compilation
as semantic validation.

The review checked the ring map, both prime ideals and the exact lies-over condition;
R and H use the recorded generalized ordinary-henselization predicate; the auxiliary
algebra instances force the canonical structural maps. The first two output equations
fix the structural residue isomorphisms. The h clause includes the local extension
and uniqueness. The formulas for ε and εT use the same residue map of p -> q and
the residue of each tensor's second factor. The kernel is not an arbitrary prime,
and both prime contractions are explicitly present. iD is a residue equivalence
with its structural equation. Both ind-etale claims concern the correct B-maps.
α exists unconditionally and is characterized on R and B_q. The e clause is inside
the henselian-D implication and its uniqueness checks only locality, B-linearity,
and residue identity; the R compatibility is then separately concluded. Finally
`e.symm.trans α` has the correct orientation H -> T_(n_T) and its equations check
both factors. The alias has real localization data and an existing prime proof;
the sole postponed proof is the named main theorem with its source/proof docstring.

No mathematical mismatch was found in this pass. I added the direct public import
of `Mathlib.RingTheory.Localization.AtPrime.Basic` so the recorded localization
dependency's module is explicitly imported, not merely available transitively.
