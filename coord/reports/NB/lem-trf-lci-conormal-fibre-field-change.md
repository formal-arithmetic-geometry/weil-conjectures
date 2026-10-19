## Worker report

Item: lem-trf-lci-conormal-fibre-field-change. The delivery states
`Algebra.Generators.conormal_fibre_field_change` in
`lean/Sheaf/RingTheory/ConormalFibreFieldChange.lean`. Its only postponed theorem is this
statement, with proof `sorry`; the docstring records all eight DAG proof steps and their
sources. Only the item's `lean` field changes. No statement correction, new node, dependency
repair, or STATEMENT-DISPUTED is needed.

The source was read in the local Stacks algebra.tex, Tag 00SI, lines 36215–36259, including
the prime contractions and residue-field dimension comparison. The conormal formulation is
also explained by Tag 00SJ and the flat conormal comparison, Morphisms Tag 0473. The source
uses the ideal fibre at the inverse-image polynomial prime; passage to I/I² at the quotient
prime is the conormal version already stated by this DAG node.

Hypotheses and objects, clause by clause:

- The fields k and K and their extension are `[Field k] [Field K] [Algebra k K]`.
  Their universes u and v are independent, and C has its own universe w.
- The finite-type commutative k-algebra C is `[CommRing C] [Algebra k C]
  [Algebra.FiniteType k C]`.
- The chosen finite-variable polynomial surjection is
  `P : Algebra.Generators k C (Fin n)`, for arbitrary `n : ℕ`. Its polynomial ring is
  `MvPolynomial (Fin n) k`, its surjection is `MvPolynomial.aeval P.val`, and its
  kernel is `P.ker`. This is Mathlib's existing presentation interface, not a new notion.
  It imposes no condition beyond a chosen surjection: any π and its surjectivity proof
  give `Algebra.Generators.ofAlgHom π hπ`, whose kernel is π's kernel by
  `Algebra.Generators.ker_ofAlgHom`. The bundled set-theoretic section does not restrict π.
- The extended algebra is literally `K ⊗[k] C`. The polynomial presentation is
  `P.baseChange K`; its variables map to `1 ⊗ₜ P.val i` by `baseChange_val`.
  Its kernel is the coefficientwise extended ideal I_K. This is the same base-change
  construction underlying the recorded `Algebra.Presentation.baseChange` dependency:
  its relations are the coefficientwise images, and their span is the kernel.
  No independent presentation, arbitrary comparison, or quotient identification is assumed.
- `Q : Ideal (K ⊗[k] C)` and `[Q.IsPrime]` give q_K. The prime q is
  `(q : Ideal C) [q.IsPrime]`, with
  `hq : q = Q.comap Algebra.TensorProduct.includeRight.toRingHom`.
  Thus it is precisely the contraction along c ↦ 1 tensor c. The two polynomial primes
  q' and q_K' are their inverse images under the two presentation maps; they are not
  extra independent data and do not occur in the node's conormal-fibre conclusion.
- `P.toExtension.Cotangent` is exactly I/I², with the existing Mathlib quotient C-action.
  `(P.baseChange K).toExtension.Cotangent` is I_K/I_K², with its C_K-action.
  `LocalizedModule q.primeCompl ...` and `LocalizedModule Q.primeCompl ...` are the
  required module localizations. They are retained explicitly.

Conclusion and canonical map, clause by clause:

- Write V for `q.ResidueField ⊗[Localization.AtPrime q]
  LocalizedModule q.primeCompl P.toExtension.Cotangent` and W for the corresponding
  expression at Q and the extended presentation. These are the displayed residue fibres,
  with the two tensor factors swapped to put the scalar field first. This is the standard
  tensor symmetry over a commutative ring; no module is replaced by a different fibre.
- `conormalFibreFieldChangeSource` is exactly `Q.ResidueField ⊗[q.ResidueField] V`,
  again the node's source with the outer tensor factors swapped. Its body installs
  `(Ideal.ResidueField.map q Q includeRight.toRingHom hq).toAlgebra` explicitly.
  This is the induced residue-field embedding, not a quantified or chosen field map.
  The two global named instances give this concrete tensor its existing additive group
  and Q.ResidueField-module structure. They contain real Mathlib tensor data.
- `∃ e : ... ≃ₗ[Q.ResidueField] W` states the required vector-space isomorphism.
  `conormalCoefficientExtension` is the concrete map on I/I²: the composite of
  `Extension.toBaseChange` with `Generators.baseChangeFromBaseChange`, passed through
  `Extension.Cotangent.map`. The first map is tensor inclusion; the second is
  `MvPolynomial.algebraTensorAlgEquiv`. Their composite fixes variables and applies
  k → K to coefficients. This gives precisely f mod I² ↦ image(f) mod I_K².
- `conormalFibreFieldChangeTmul ... x a b` is literally
  `b ⊗ₜ (a ⊗ₜ LocalizedModule.mk x 1)` under the canonical scalar structure.
  The first conjunct says its image is `(b * residueMap a) ⊗ₜ
  LocalizedModule.mk (conormalCoefficientExtension x) 1` for every conormal class x
  and all residue scalars a,b. In particular x = `Extension.Cotangent.mk f`, a = 1
  is the node's prescribed image of (f mod I²) tensor λ. The more general formula
  follows from tensor balancing and linearity, so it adds no mathematical conclusion.
  These elements span the source: localization denominators become nonzero residue
  scalars, and conormal classes and pure tensors generate the relevant modules.
  Consequently this formula specifies the canonical coefficient-extension isomorphism.
- `Module.Finite q.ResidueField V` and `Module.Finite Q.ResidueField W` assert finite
  dimensionality over the respective fields. The final equality is
  `Module.finrank q.ResidueField V = Module.finrank Q.ResidueField W`, the finite
  dimension equality of the node's proof. Together with e this also implies that both
  displayed Q.ResidueField-vector spaces have this same finite dimension.

Dependency interfaces used (full signatures and docstrings read):

- def-weil-pbc-finite-type-algebra: `Algebra.FiniteType` and `RingHom.FiniteType`,
  Mathlib.RingTheory.FiniteType. The algebra-instance form is the node's equivalent
  algebra formulation; the latest record's bare-ring-map form remains usable.
- def-weil-pbc-mv-polynomial-ring: `MvPolynomial`, `MvPolynomial.aeval`,
  `MvPolynomial.algHom_ext`, Mathlib.Algebra.MvPolynomial.Basic/Eval.
- def-weil-pbc-localization-at-prime: `Localization.AtPrime` and `Ideal.ResidueField`,
  Mathlib.RingTheory.Localization.AtPrime.Basic and
  Mathlib.RingTheory.LocalRing.ResidueField.Ideal; the latter also supplies the
  canonical `Ideal.ResidueField.map` used here.
- def-weil-pbc-module-localization: `LocalizedModule`, `LocalizedModule.mk`,
  Mathlib.Algebra.Module.LocalizedModule.Basic.
- lem-weil-pbc-presentation-base-change: `Algebra.Presentation.baseChange`,
  Mathlib.RingTheory.Extension.Presentation.Basic, with its underlying
  `Algebra.Generators.baseChange` and the kernel/relations field. The module imports
  the recorded module publicly. No dependency repair is necessary.
- def-weil-pbc-module-tensor-product: `TensorProduct`, `TensorProduct.tmul`,
  Mathlib.LinearAlgebra.TensorProduct.Defs; the existing additive group and scalar
  extension structures are `TensorProduct.addCommGroup` and `TensorProduct.leftModule`.
- The stated proof leaves are imported without `public`: the ideal flat-conormal
  comparison in Mathlib.RingTheory.Ideal.CotangentBaseChange, faithful flatness and
  its base-change instance in Mathlib.RingTheory.Flat.FaithfullyFlat.Basic,
  polynomial regularity in Mathlib.RingTheory.RegularLocalRing.Polynomial, and
  `IsNoetherianRing` in Mathlib.RingTheory.Noetherian.Defs. There are no omitted
  stated proof dependencies or import cycles.

The five helpers belong to the canonical construction in this very node, and all are
listed in `lean.declarations`, with source/blueprint docstrings. They neither introduce an
independent mathematical notion nor postpone any theorem. Every definition has real data;
no arbitrary map, Nonempty choice, equality of universes, or extra algebraic hypothesis is
used to type the theorem.

Edge cases checked mathematically: n = 0; I = 0 (zero conormal module and dimension zero);
nonzero ideals with zero fibre; identity field extension; arbitrary transcendental and
inseparable extensions and positive characteristic; nonclosed primes; C the zero ring
(no prime Q, so the statement has no such instance); independently sized fields/algebra.
The type does not impose separability, algebraicity, perfection, positive n, maximality
of the primes, or nonzero fibre dimension. The finite-type binder and finite-variable
presentation are exactly the source data.

Searches made with msearch.py (NB, this item):

- leanfinder: “conormal fibre of ideal polynomial quotient under extension of ground
  field localized residue fields”. Eight hits included Ideal.Fiber,
  Polynomial.fiberEquivQuotient and the localization-away cotangent comparisons;
  none states this theorem with its canonical map and dimension conclusion.
- loogle: `Ideal.tensorCotangentEquiv`. Two hits, the general flat conormal
  equivalence and its tmul formula. Used as the proof leaf; it is not the localized
  residue-fibre statement.
- grep, RingTheory: `conormal.*field|cotangent.*[Ff]ield|tensorCotangentEquiv`.
  Twenty-two hits, including CotangentBaseChange and cotangent-space dimension
  facts; none is an exact match.
- leansearch: “conormal fibre of a polynomial quotient under field extension and
  equality of finite dimensions”. Eight hits on finite-dimensional quotients,
  fraction fields and quasi-finite residue fields; no exact match.
- rg over upstream WeilConjectures and this project's lean/Sheaf for conormal/fibre
  terminology found related conormal localization, smooth-fibre and geometric
  conormal results, not this statement. Exact searches for all proposed declaration
  stems in Mathlib, upstream WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json
  found no existing names. The required upstream node-id grep also had no hit.
  DAG concept search found this node and its citer, not a duplicate node.

Validation: scompile.py compiled the delivered module cleanly, both as an isolated sandbox
and under Sheaf.RingTheory.ConormalFibreFieldChange, in approximately 3.5 seconds per file.
All universes and variables are explicitly declared, all lines are at most 100 characters,
and comparison of the node JSON against the read-only repository shows only `lean` changed.

A separate scratch consumer imported the delivered module and ran `#print axioms` on
all five helper declarations. Each depends only on `propext`, `Classical.choice` and
`Quot.sound`, confirming that none of their data rests on `sorryAx`. The scratch
consumer compiled cleanly through scompile.py alongside the delivered module.

## Second reading by NB

Author's self-check, as required for direct delivery; the maintainer supplies the independent
review. I reread the node, the actual Lean file, the helper bodies, and the source signatures.
The field/algebra binders, arbitrary n, finite-variable surjection, literal K tensor C,
contracted prime equality, both conormal modules, both module localizations, both residue
tensors, canonical residue-field embedding, isomorphism, generator formula, finite dimensions
and equality of finranks each have the counterpart listed above. The inverse-image polynomial
primes are determined by the fixed presentation and do not require independent binders.
The scalar-first tensor order is only symmetry, and the generator formula fixes the map.
No hypothesis or clause was added or lost. I expanded the main theorem's full binder list
so its recorded signature is self-contained. During compilation I replaced instance
reconstruction via inferInstanceAs by the existing TensorProduct instance constants; the
final bodies construct precisely the same canonical tensor structures and compile cleanly.
