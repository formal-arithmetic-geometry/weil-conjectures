## Worker report

The module `Sheaf.Paper.RootTowerFiniteTensor` states
`AlgebraicGeometry.Scheme.rootTower_finite_tensor` with `sorry` and defines only its
projection, scalar homomorphisms, ordinary tensor and pure-tensor helpers. The retained
sandbox draft was checked against the live Q119 split. The current brief-stage2 §0
explicitly authorizes recording this stage-1 output in stage 2; the inherited stage-1
live-wins refusal does not apply. The live node has no Lean record and no repair note.
The accepted natural-language statement and all six proof steps are preserved.

Hypotheses and objects, matched individually:

- Prime ell is `(l : ℕ) [Fact l.Prime]`. The arbitrary base is `T : Scheme.{u}`.
  `hT : ∀ x : T, IsUnit (l : T.presheaf.stalk x)` means ell is invertible on T:
  invertibility is local, and a global scalar is a unit exactly when all its germs are.
- Positive level r is represented by the natural number binder `r` and exponent `r+1`.
  This includes every positive exponent, including exponent 1 when `r=0`.
- `T.ProEt` and `ProEt.topology T` are the recorded small pro-etale site with object
  universe u+1 and morphism universe u. No universe equality is imposed.
- `proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)` is the recorded tower,
  level s corresponding to exponent s+1. Its transitions are the ell-th power maps.
  `purTwistZlOne T l` is literally its categorical limit. `rootTowerProjection`
  is `limit.π` of that very diagram, not another inverse-limit construction.
- The scalar `purTwistZlConstant T l` is the constant discrete ring sheaf of ULift Z_l.
  The existing coordinatewise action `purTwistZlModule` is restricted along
  `purTwistZlCompletionMap`. That map is fixed by every finite reduction, so its action
  on the s-th root coordinate is precisely the residue action specified by the node.
  This uses the constant ring, not the completed coefficient ring, in the tensor.
- The constant residue coefficient is `purTwistFiniteRing T l r`, the constant sheaf
  of ULift (ZMod (l^(r+1))). The finite roots module is `purTwistRootsModule`, which
  transports the recorded roots module across the canonical constant-ring comparison.
- `B : Type (u+1)`, `[CommRing B]`, `[Algebra ℤ_[l] B]` express an arbitrary commutative
  Z_l-algebra in the containing coefficient universe. Small coefficient rings can be
  lifted there. There is no finiteness, flatness, nonzero, or dimension hypothesis.
  `hB : ((l^(r+1) : ℕ) : B) = 0` is exactly ell^(r+1) B = 0 for a unital ring.
  `rootTowerResidueScalar` is the unique ZMod-to-B scalar map, using the characteristic
  divisibility certified by hB. Its composite with Z_l reduction is the given algebra
  map: both maps factor through the same cyclic quotient. No arbitrary scalar map is
  quantified over.

Conclusion clauses, matched individually:

1. `Sheaf.IsLocallySurjective (rootTowerProjection T l r)` is local surjectivity on
   the site's covering sieves, hence exactly on pro-etale covers.
2. For every `U` and every section `x`, the first universal conjunct states projection
   zero iff `∃ y, l^(r+1) • y = x`. This is both inclusions of the sectionwise kernel
   equality. Additive zero is the unit root 1 in multiplicative notation.
3. The existential function `d` has domain exactly that sectionwise kernel. Its first
   clause equates the included s-th coordinate of `d U x` with the included higher
   coordinate of x. The higher Lean index is `s+r+1`, whose exponent is `s+r+2`;
   this is the source exponent `(s+1)+(r+1)`. Equality is in the common units sheaf
   using `proEtaleRootsOfUnityInclusion`, since different root groups have different
   types. Thus it specifies the actual shift, including that it lands in the lower
   roots group. The second clause is division `l^(r+1) • d U x = x.val`.
   The final implication states compatibility for every restriction `f : V ⟶ U`;
   `y.val` is explicitly required to be the restriction of x, with its kernel proof.
4. `rootTowerTensor` is change of rings of the restricted limit module from constant
   Z_l to `tateFiniteCoefficient T B`, and hence is H in the statement.
   `tateFiniteLine T l B r (rootTowerResidueScalar ... hB)` is the ordinary finite
   root tensor over constant Z/l^(r+1). Both use the published sheafification of the
   sectionwise tensor; scalar extension writes the B factor first.
5. `∃ e : rootTowerTensor ... ≅ tateFiniteLine ...` is an isomorphism of B-sheaves.
   The immediately following equality on every U, b and x specifies e.hom by
   `x tensor b ↦ p_r(x) tensor b`. The equality characterizes the canonical alpha,
   rather than asserting that some unrelated isomorphism exists.
6. The last clause quantifies over every covering sieve S, every family of lifts x,
   every finite root a, every coefficient section b and every candidate global h.
   It says h restricts to all the lifted tensors iff h is e.inv applied to a tensor b.
   This is existence and uniqueness of the gluing simultaneously, and therefore
   independence of both lifts and covers. It does not assume the lifts themselves
   are a compatible family; their tensors become compatible by the kernel equality.

Dependency declarations read and reused:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` and scheme morphisms.
- Mathlib.AlgebraicGeometry.Sites.Proetale: `Scheme.ProEt`, `ProEt.topology`.
- Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf: the recorded root sheaf,
  its inclusion, module, transition and tower; their full signatures and docstrings
  identify roots as the kernel of the actual units power map.
- Mathlib.CategoryTheory.Limits.HasLimits: `limit`, `limit.π`.
- Mathlib.CategoryTheory.Sites.ConstantSheaf: `constantSheaf`.
- Mathlib.NumberTheory.Padics.PadicIntegers and RingHoms: `PadicInt`, `toZModPow`.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses: the recorded
  ordinary sheaf tensor interface, publicly exposing TensorProductOfUniverses;
  its `changeOfRingsOfUniverses` is sheafification of sectionwise extension of scalars.
- Sheaf.Paper.PurTwistCoefficientRings: `purTwistZlConstant`, `purTwistFiniteRing`,
  `purTwistZlCompletionMap` and its defining unique finite-reduction characterization.
- Sheaf.Paper.PurTwistSheaves: `purTwistZlOne`, `purTwistZlModule`,
  `purTwistZlAction_existsUnique`, `purTwistRootsModule`.
- Sheaf.Paper.TateTwistLocallyFree: only the unconditional definitions
  `tateFiniteCoefficient`, `tateFiniteScalar`, `tateFiniteLine`, `tateFiniteTensor`
  are used; the finite-coefficient theorem is not applied to arbitrary B.
- Sheaf.Paper.PurInverseImageTensorHomDefinitions (publicly through the above
  module): `purScalarSection`, the sheafification image of the actual pure tensor.

The owning landed definition nodes for these interfaces are added to stmt_deps under
brief-stage2 §5 (landed nodes may be added). A traversal of their statement and proof
edges found no path back to this item. No dependency node is modified, no notion is
copied, and no new definition node is needed: the helpers merely specialize existing
constructions to the exact objects already introduced in this item's statement.
Proof imports include the recorded Kummer, etale comparison, repleteness and local
sheafification modules. The theorem docstring carries all six accepted proof steps.

Edge cases checked: the empty scheme and empty test object have their unique sections;
zero coefficient ring gives zero tensor sheaves; exponent 1 is Lean r=0; ell=2 is
included; B=Z/ell at exponent 2 is allowed despite being nonflat over Z/ell²; no
connectedness, affineness, quasi-compactness or global compatible primitive root is
assumed. Surjectivity is local, not claimed on all original U. The shift arithmetic
was checked for s=r=0: the second root coordinate supplies a first-root coordinate.
The gluing iff includes the identity covering and every refinement.

Sources read: Stacks proetale.tex lemma-proetale-enough-w-contractible (0990),
etale-cohomology.tex lemma-kummer-sequence (03PL), and the node's accepted agent
shift/tensor arguments. As the node already explains, 0990 does not itself state
those agent arguments. There is no statement correction or disputed clause.

Searches performed through msearch.py and source rg:

- LeanSearch: "Inverse limit roots of unity sheaves tensor with an algebra killed
  by a prime power is the tensor of finite roots of unity". Eight hits include
  TensorProduct.directLimitLeft/Right, SheafOfModules.hasLimit and algebraically
  closed field roots. None states the normalized inverse-limit sheaf result.
- LeanFinder: "Inverse limit roots of unity sheaves tensor with a torsion algebra
  agrees with the finite roots sheaf with normalized local lifts". Eight hits concern
  number-field unit torsion, cyclotomic characters, roots maps and light condensed
  monoidal structures; none is this statement.
- Loogle: `"TensorProduct", "quotient"`. Twelve hits give algebraic module quotient
  tensor equivalences, not root-sheaf local lifting and normalized descent.
- Mathlib grep: `rootsOfUnity|TateModule|proetale`, AlgebraicGeometry. Ten hits
  include Proetale and ElladicCohomology; neither states this lemma.
- Source rg in both lean/WeilConjectures and lean/Sheaf for
  `rootTower_finite_tensor|rootTowerProjection|rootTowerTensor|finite.*tensor.*root|root.*tensor.*finite`
  found only unrelated DVR tensor facts and finite Cartier comparison maps.
  grep of this blueprint id in WeilConjectures found no hit. The Cartier finite
  root map does not contain an inverse-limit projection or the shift-kernel assertion.

Validation: scompile.py compiled the delivery as both sandbox and library module,
cleanly. The initial cast-of-power elaboration error was repaired by writing the
annihilation premise as the natural-number power cast to B; no extra theorem or
proof was introduced. Every definition has real data; the only postponed proof is
`rootTower_finite_tensor`, matching this node. No sub-agents or independent second
reading were used; the maintainer performs the independent review after delivery.

## Returned-delivery repair

Repaired the H2 finding in the independent review of immutable head
`3e715d439ac7`. The two statement dependencies now cite the owning definition
nodes already on the base:

- Replaced `det-def-sp-tate-twist-locally-free` by
  `def-pur-finite-tate-line-signed-comparison`. Its existing Lean record owns
  `tateFiniteCoefficient`, `tateFiniteScalar`, `tateFiniteLine` and
  `tateFiniteTensor` in `Sheaf.Paper.TateTwistLocallyFree`. Their complete
  signatures and bodies have no finiteness assumption on B. The locally-free
  theorem is not used to state this item.
- Replaced `lem-pur-isomorphism-inverse-image-tensor-hom` by
  `def-pur-inverse-image-tensor-hom-sections`. Its Lean record owns
  `purScalarSection` in `Sheaf.Paper.PurInverseImageTensorHomDefinitions`,
  the actual pure scalar tensor followed by module sheafification.

The other nine statement dependencies are retained. Against the current shared
base, only `stmt_deps` and `lean` differ; the additions all name landed definitions.
This is the requested worker repair of the returned packet, rather than a
maintainer stage-2 FIX. No dependency node or mathematical statement is changed.
The Lean module and its recorded signature remain byte-identical to the retained
packet; the module SHA256 is
`e638b2d7b9dae00b76f5de726a9db3cfc773e9c177a466f634566021294c48fb`.
The initial saved-packet dry run passed at `d5b8b028d93`; that mechanical pass
preceded this required repair and did not discharge the independent H2 finding.

Repair validation: `scompile.py Q110 lem-amb-root-tower-finite-tensor` compiled
`RootTowerFiniteTensor.lean` cleanly in both sandbox (13.5 s) and library
(15.9 s) modes. The self-check verified all eleven dependency ids, retention of
the other nine, verbatim recorded theorem signature, the unchanged module hash,
and that only `lean` and `stmt_deps` differ from the current base node.

## Second reading by Q110

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
