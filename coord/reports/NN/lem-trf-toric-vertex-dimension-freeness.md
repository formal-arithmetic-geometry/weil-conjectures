## Worker report

Stage 2 repair, NN, 2026-10-23, of the independent review at immutable head 3955c2004c0c. The saved packet was retained and its initial dry run passed. The H2 return is repaired below; the accepted split and mathematical statement are unchanged.

The new module is `Sheaf.RingTheory.ToricVertexDimensionFreeness`. The main statement is `AddMonoidAlgebra.toricVertex_dimension_freeness`. Its only new postponed results are that theorem and `toricVertexIdeal_isMaximal`, the named proof obligation needed to construct the actual localization in the statement. The latter is precisely the maximality calculation in this node's proof step 4, with the complete kernel/evaluation proof in its docstring. The ideal and localization helpers belong to the explicitly introduced objects of this node; neither defines a new independent mathematical notion. Definitions have real data. Nothing is proved in the new module.

Read the whole item, all nine statement-dependency statements and their Lean/mathlib records, the relevant full declarations and docstrings, and the proof-dependency interfaces. Read the source directly using pdftotext on PDF pp.110--111 (printed pp.104--105), including the entire proof of ILO VIII 3.2.12(ii). The rank/dimension and torus-factor expansion is the accepted DAG split. The current latest blueprint and unit record identify this as historical supporting toric work, not the unit's own contracting-correspondence statement. The withdrawn CompactObject example is only a header example here.

Hypothesis and object correspondence:

- The field is `(k : Type u) [Field k]`; the monoid is `(R : Type v) [AddCommMonoid R]`, with independent explicitly bound universes, so no size or characteristic restriction is introduced.
- Fineness is `hfine : AlgebraicGeometry.FineFan.IsFine (Multiplicative R)`, the recorded predicate. Multiplicative is only the notation conversion to the recorded multiplicative convention. Its data is finite generation and injectivity into the canonical Grothendieck group.
- Sharpness is exactly `hsharp : FineFan.IsSharp (Multiplicative R)`, not a private version. The only additive unit is zero.
- Saturation is `hsat : (MonoidHom.mrange (Algebra.GrothendieckGroup.of ...)).PowSaturated`, the same root-saturation convention used by `FineFan.Fan.IsSaturated`.
- Torsion-freeness is `[IsMulTorsionFree (Algebra.GrothendieckGroup (Multiplicative R))]`. For an abelian group this is exactly absence of nonzero finite torsion, including every positive natural exponent.
- The finite rank and finite torus rank are `r t : ℕ`. `hr` identifies `Module.finrank ℤ` of the additive Grothendieck group with `r`. Fineness and torsion-freeness ensure this is a finite free Z-module, so this finrank is its ordinary lattice rank, including rank zero.
- The finite atom set is `A : Finset R`, and `hA : ∀ q, q ∈ A ↔ AddIrreducible q`. Mathlib's predicate means not an additive unit and every decomposition has an additive unit summand. Under the recorded sharpness condition this is exactly nonzero and not a sum of two nonzero elements. Its finiteness is the Finset data, with no order or enumeration chosen. `hgen : AddSubmonoid.closure (A : Set R) = ⊤` is generation as a monoid.
- `B` is written explicitly as `AddMonoidAlgebra k (R × (Fin t → ℤ))`. The bijection of monomial bases `(q,h) ↦ e^q ∏ y_j^(h_j)` is the Laurent algebra presentation in the node and its proof step 1; it is not a different abstract algebra with an arbitrary comparison map.
- `toricVertexIdeal k R t` is literally the ideal span of the nonzero R-monomials and of `single (0, Pi.single j 1) 1 - 1`, namely y_j-1. It is not an arbitrarily specified ideal.
- `ToricVertexLocalRing k R t hsharp` is exactly `Localization.AtPrime` at that ideal. The named maximality theorem supplies its proof of primality. Thus primality/maximality is not an extra hypothesis and no localization data is chosen by existence.
- `hcot` states the required dimension `A.card + t` of `IsLocalRing.CotangentSpace` of the localization. Mathlib defines this as its maximal ideal modulo its square, over `IsLocalRing.ResidueField`. The evaluation map in source/proof step 4 canonically identifies that residue field with k, so residue-field dimension is precisely the stated k-dimension. No independent scalar action or residue-field identification is assumed. Finite dimensionality is automatic here from finite generation of the monoid algebra over a field.

Conclusion correspondence, in conjunction order:

- `Algebra.FiniteType k B` is the required finite type algebra predicate, from the recorded finite-type module (and its unchanged mathlib_match).
- `IsDomain B` is the integral-domain assertion.
- `Nonempty (FractionRing B ≃ₐ[k] FractionRing (MvPolynomial (Fin (r+t)) k))` says its actual fraction ring is isomorphic over k to the rational function field in exactly r+t variables. This is the rational-function-field form of the recorded purely transcendental definition, retaining the specified number of variables. The preceding IsDomain clause makes this fraction ring a field; no abstract field with arbitrary algebra structure replaces it.
- `ringKrullDim (ToricVertexLocalRing ...) = ((r+t : ℕ) : WithBot ℕ∞)` is the dimension assertion using the recorded definition and all three possible infinite/bottom dimension values excluded by the finite equality.
- The implication starts with exactly `IsRegularLocalRing (ToricVertexLocalRing ...)`, Mathlib's Noetherian regular local ring predicate from the recorded regularity dependency's unchanged ring match.
- Its first conclusion is `A.card = r`.
- Its second is the existence of `Module.Basis A ℤ` of the actual additive group completion, with the additional equation `b a = Additive.ofMul (GrothendieckGroup.of (Multiplicative.ofAdd (a : R)))`. The equation fixes every basis vector to the image of its atom; a bare existence of some basis would lose this clause.
- Its final conclusion is an additive equivalence `e : (A → ℕ) ≃+ R`, with `e n = ∑ a : A, n a • (a : R)` for every tuple. Thus the specified canonical homomorphism N^A→R is an isomorphism, not merely a noncanonical isomorphism of its source and target. Since A is finite, functions on A are the finite free commutative monoid's coefficient tuples.

Dependencies used, with recorded modules and names:

- `Sheaf.AlgebraicGeometry.FineFanBlowup`: `AlgebraicGeometry.FineFan.IsFine`, `IsSharp`; its group-completion/range saturation convention. This module is repaired only for module mode below.
- `Sheaf.AlgebraicGeometry.MonoschemeToricRealization`: `AlgebraicGeometry.Monoscheme.monoidAlgebra` and the monomial convention (its object is Mathlib MonoidAlgebra, with AddMonoidAlgebra the additive presentation). Repaired only for module mode below.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`, provided publicly also through regular-local definitions.
- `Sheaf.AlgebraicGeometry.IsRegularScheme` and `Mathlib.RingTheory.RegularLocalRing.Defs`: the dependency's ring clause `IsRegularLocalRing`, and `IsRegularLocalRing.iff_finrank_cotangentSpace` for its recorded Mathlib proof dependency.
- `Mathlib.RingTheory.FiniteType`: `Algebra.FiniteType` / `RingHom.FiniteType`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`; `IsLocalRing.ResidueField` and `CotangentSpace` through the regular-local/cotangent imports.
- `Mathlib.LinearAlgebra.Dimension.Finrank`: `Module.finrank`.
- `Mathlib.LinearAlgebra.FreeModule.Basic`: `Module.Free`, `Module.Basis`.
- `Sheaf.FieldTheory.PurelyTranscendentalExtension`: `Algebra.IsPurelyTranscendentalExtension`; its equivalent rational-function-field form is used, with the exact finite variable count in the statement.
- Retained proof imports: `WeilConjectures.RingTheory.FiniteTypeDomainDimensionTrdeg`, `finiteType_domain_ringKrullDim_eq_trdeg`; `Mathlib.LinearAlgebra.FreeModule.PID`, `Module.basisOfFiniteTypeTorsionFree'`; `Mathlib.RingTheory.OrzechProperty`, `OrzechProperty.bijective_of_surjective_endomorphism`. The fraction-field theorem is a proof dependency only; its legacy import is omitted as explicitly requested by return H2, and its base file and node record are restored byte-identically. The lattice-torus coordinates node has no recorded Lean declaration, Mathlib match or usable source declaration, and is only a proof dependency: its future import is omitted, and no premise from that unstated theorem is needed to type this statement. The explicit monomial-coordinate proof is documented for stage 3.

Edge cases checked before writing: R=0, A empty, r=t=0 gives B=k and a dimension-zero field localization; R=0 and t>0 gives the torus identity with maximal ideal (y_j-1) and dimension t; R=N^r gives the polynomial-times-torus local ring and the standard atom basis; singular saturated lattice-cone monoids may have more atoms than rank, and the regularity implication consequently has false antecedent rather than asserting freeness. For characteristic p the Laurent generator y_j-1 still has a nonzero linear coefficient; no exponent differentiation or division by an integer is assumed. Empty sums, Fin 0, and bases indexed by an empty Finset are all permitted by the signature. No field is required algebraically closed or perfect, and no assumption asserts regularity unless taking the final implication.

Searches made on 2026-10-23:

- msearch.py leanfinder, query: “The local dimension of a sharp affine monoid algebra at its toric vertex equals the lattice rank; regularity forces the atoms to be a free basis.” Eight hits included AffineAddMonoid.dim, Module.rankAtStalk_self, standard smooth dimension, and lattice rank results; none states the vertex dimension/freeness theorem.
- msearch.py loogle, query `"AddMonoidAlgebra", "IsRegularLocalRing"`: zero hits.
- msearch.py grep, query `toric.*regular|regular.*toric|monoid.*krullDim`, RingTheory: zero hits.
- rg across both project roots for the item id, toricVertex, toric_vertex, and vertex ideal/atom monomial terminology: no matching declaration. Broad toric searches located the parent ToricMonoidComparison, formal complete toric models, and positive grading; read the parent's full smoothness-reflection statement and its proof docstring. It concerns a smooth toric realization and is not this local algebra theorem. No duplicate exists.
- Read Mathlib's AddIrreducible definition and use it instead of defining an atom predicate. Read the finrank, finite type, basis, regular-local cotangent and localization definitions and recorded generic proof theorem signatures. Search of dag/lean_names_upstream.json and both project roots for all four new declaration names found no clashes.

No STATEMENT-DISPUTED finding and no statement correction. The item's stmt_deps is restored exactly to the base list: lem-trf-monoid-algebra-domain-fraction is present only in proof_deps. No proof, proof_deps, statement, source, reviewed, status, or any other original field changes.

## Dependency modules

`def-trf-fine-fan-blowup`: the recorded file is a legacy non-module file. A server module-mode compile rejected the exact import with `cannot import non-\`module\` Sheaf.AlgebraicGeometry.FineFanBlowup from \`module\``; `scompile.py --source` confirms the live source, not merely a stale local checkout. Under §1(B) its sandbox copy adds `module`, public visibility to the original imports, and `@[expose] public section`. All original declarations, signatures, bodies and proof terms are unchanged. The node changes only in lean, with a note explaining the unusable interface and exact repair. No copy of its mathematical notions is introduced.

`def-trf-monoscheme-toric-realization`: its recorded file is likewise legacy non-module and is a statement import required by the brief. The same conversion preserves every declaration, including all previously repaired realization maps and canonical torus embeddings. Its existing mathematical content is neither weakened nor restated. Only lean changes in the node, documenting the module-mode repair.

The former conversion of `lem-trf-monoid-algebra-domain-fraction` is withdrawn: both its node and module are byte-identical to the current base, so neither contributes a delivery diff. Only the two definition dependencies above are converted.

Validation before repair: the saved four-file packet passed deliver2.py --no-push. The corrected packet is recompiled and dry-run below. All binders and universes in the new module are explicit with autoImplicit false. Existing proof terms in the two preserved definition interfaces are unchanged.


## Returned H2 repair

The independent review at 3955c2004c0c accepted the mathematical statement and both definition-module conversions. It returned only the proof-only module conversion. Removed `lem-trf-monoid-algebra-domain-fraction` from stmt_deps, restored its node (including its lean record) and its Lean file byte-identically to the current base, and removed `import Sheaf.RingTheory.MonoidAlgebraDomainFraction` from the item. Its proof_deps entry and the source-based proof docstring remain. The FineFanBlowup and MonoschemeToricRealization conversions and all four item declarations are retained unchanged.

Self-check: opened the node and complete module. The field, fine/saturated/sharp monoid, torsion-free group completion, rank r, finite generating atom set, torus rank t, canonical vertex ideal/localization and cotangent-dimension hypothesis still match exactly. The finite type, domain, r+t-variable rational function field, Krull dimension, and conditional cardinality, atom-pinned integral basis and sum-pinned monoid isomorphism conclusions are verbatim unchanged. The maximality obligation still uses sharpness alone. Empty atoms, R=0, r=t=0 and positive characteristic remain covered.

Repair validation: scompile.py compiled all three changed modules separately against the live published build and private overlays, with no errors or warnings. The recorded theorem signature is byte-for-byte the module signature; stmt_deps equals the current base, and proof_deps is unchanged. Both withdrawn dependency files are byte-identical to base. The next deliver2.py dry run verifies the complete packet.

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
