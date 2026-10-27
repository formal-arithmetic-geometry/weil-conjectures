## Worker report

The module `Sheaf.AlgebraicTopology.OrderedJoinPrefixTelescope` states
`AlgebraicTopology.orderedJoinPrefixTelescope`, with its only theorem proof `sorry`.
Its two real-data helpers define exactly the prefixes and homotopy already introduced
in this node, rather than introduce any independent notion. The node statement and
its dependency lists are unchanged.

Hypotheses and constructions, clause by clause:

- `r : ℕ` and `hr : 1 ≤ r` render r≥1; `Fin r` is precisely I={0,...,r-1}.
- `A : ChainComplex (ModuleCat.{u} ℤ) ℤ` supplies the integer-indexed abelian groups
  regarded as integer modules, and their differential with d²=0. In particular
  `A.d q (q-1) ≫ A.d (q-1) ((q-1)-1) = 0` is `A.d_comp_d`.
  The bundling introduces no hypothesis: any family and square-zero degree-minus-one
  maps in the node defines such a complex by setting nonadjacent components to zero.
  Conversely the complex's only potentially nonzero components are these adjacent maps.
  Integer-linear maps are exactly homomorphisms of abelian groups.
- `c : ∀ i q, A.X q ⟶ A.X (q+1)` is precisely the family c_i,q, without a chain-map
  or contraction assumption. `R : ∀ i q, A.X q ⟶ A.X q` gives all remainders.
- `hlocal` is d_(q+1)c_i,q+c_i,(q-1)d_q=id-R_i,q for every i and integer q.
  In Lean, `f ≫ g` applies f first, so the categorical expression reverses the
  written order of ordinary function composition. `A.d (q+1) q` is d_(q+1).
  The final `(A.XIsoOfEq (sub_add_cancel q 1)).hom` only identifies
  A_((q-1)+1) with A_q, canonically. It asserts no extra identification of groups.
- `orderedRemainderPrefix A R n q` folds the list of the first n entries of
  `List.finRange r`. The fold step is `P ≫ R i q`, namely R_i composed with P
  for the inner suffix. Expanding n=2 gives `(id ≫ R_1) ≫ R_0`, or R_0∘R_1.
  Thus P_0=id and P_(i+1)=P_i∘R_i exactly. Only n≤r is asserted by the theorem.
- `orderedPrefixHomotopy A c R q` is the finite sum
  `∑ i, c i q ≫ orderedRemainderPrefix A R i.val (q+1)`, namely ∑ P_i,q+1∘c_i,q.

Conclusions, clause by clause:

- The first conjunct quantifies over every integer q and `i : Fin r` and states
  `R i q ≫ A.d q (q-1) = A.d q (q-1) ≫ R i (q-1)`, exactly dR_i=R_i d.
- The second conjunct quantifies over every q and `n : ℕ` with n≤r and states
  the corresponding commutation formula for P_n. Both n=0 and n=r are included.
- The third conjunct is d_(q+1)H_q+H_(q-1)d_q=∑(P_i,q-P_(i+1),q) for every q,
  with the same canonical degree identification as in hlocal.
- The fourth conjunct is ∑(P_i,q-P_(i+1),q)=id-P_r,q for every q. Together these
  are both equalities in the displayed chain of equalities of the node.
- The last conjunct fixes an arbitrary degree q and a family `S` of additive
  subgroups indexed by `{C : Set (Fin r) // C ⊂ Set.univ}`, exactly all proper
  color subsets. Its first premise expresses finite-sum generation explicitly:
  each x is a sum of an n-tuple f, each f_j lying in a chosen S_(C_j).
  The tuple length may be zero and the colors may repeat, as finite sums allow.
  Its second premise is preservation `x ∈ S C → R i q x ∈ S C` for every i,C,x.
  Its third premise is `i ∉ C.val → x ∈ S C → R i q x = 0` for every i,C,x.
  The conclusion is precisely `orderedRemainderPrefix A R r q = 0` as a map.
  These hypotheses are confined to the arbitrary fixed degree, not imposed in
  other degrees or on the preceding commutation and telescoping conclusions.

Dependencies read and used:

- `def-weil-pbc-module-chain-complex-homology` records
  `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`,
  `HomologicalComplex.homology`. Its complete source and docstring were read.
  The node's `mathlib_match.how` specifies `ChainComplex (ModuleCat R) ℤ`,
  `HomologicalComplex.Hom`, and adjacent differentials as the actual chain model.
  This delivery uses that exact `ChainComplex` specialization, `A.X`, `A.d`,
  and `A.XIsoOfEq`; it does not need to take homology. The recorded module is
  publicly imported. The square-zero hypothesis is encoded in that same complex,
  not replaced by a private definition. There are no other proof dependencies.
- `Mathlib.Algebra.Category.ModuleCat.Basic` supplies integer-module morphisms
  and their additive structure; `Mathlib.Data.List.FinRange` supplies the canonical
  increasing list of colors. The corresponding definitions were read in source.

Source check: read the current `literature/blueprint/latest/blueprint/`
`sec-six-functors-basics/sk-thm-sf-ctf-stability/`
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3).
As the node explicitly says, this abstract lemma is an agent generalization
below that paragraph, rather than an assertion made by the blueprint. The full
five-step argument in the DAG is reproduced in the theorem docstring.

Edge cases checked before writing and again against the final signature:

- At r=1 the only proper color subset is empty. Preservation is meaningful,
  the vanishing premise kills its subgroup, and finite-sum generation kills A_q.
  P_1=R_0 and H=c_0, agreeing with the stated identity.
- P_0 is the empty fold, hence the identity. The sums use all of Fin r exactly
  once; P_r includes every factor. No pairwise commutation is assumed or used.
- The zero group and the zero-length finite sum are included.
- All integer degrees, including negative degrees and q=0, are quantified.
  The shift cast is valid for every integer and does not truncate the complex.
- Each proper subset omits a color because Fin r is finite. Factors applied
  before that omitted color preserve its subgroup; no order rearrangement is needed.
- A heterogeneous family of groups is permitted: the only transport is along the
  arithmetic equality (q-1)+1=q, so the statement does not require constant A_q.

Searches made (2026-10-24 UTC; the wrapper's returned results were inspected):

- `msearch.py leanfinder`: "An ordered sum of prefix products composed with local
  chain homotopies telescopes to identity minus the ordered product, vanishing on
  invariant proper color subgroups". Eight hits, including Dold-Kan `P_add_Q`,
  `homotopyPToId`, `Q_succ`, and specialized Nobeling maps. None states this
  abstract ordered formula and the support-vanishing clause.
- `msearch.py leansearch`: "An ordered finite product of chain maps homotopic to
  identity is homotopic to identity by a sum of prefix homotopies". Eight hits,
  including `Homotopy.compLeftId`, `Homotopy.trans`, and
  `Homotopy.comp_nullHomotopicMap'`; no exact match.
- `msearch.py loogle`: `Homotopy.comp, List.take, List.prod`; zero hits.
- `msearch.py grep`: `(telescop|prefix).*(homotop|chain)|`
  `(homotop|chain).*(telescop|prefix)` over Mathlib. Only
  `Mathlib/Data/List/Chain.lean:251` (`IsChain.prefix`), unrelated to complexes.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf`, and the upstream declaration
  index, for ordered prefixes/telescopes and the item id: no general statement.
  The module `Sheaf.AlgebraicTopology.OrderedJoinPartialContraction` defines the
  special ordered-join-chain `remainderPrefix` and `contraction`; its full source
  was read. Those take pointed vertex families and their specifically constructed
  free groups and remainders, so cannot express the arbitrary A,c,R of this node.
- `grep -rn` for this item's exact id in `lean/WeilConjectures`: no matches.
- `rg` over Mathlib, both project source roots, and the upstream declaration index
  for `orderedRemainderPrefix|orderedPrefixHomotopy|orderedJoinPrefixTelescope`:
  no existing declarations with these names.

No statement dispute, node correction, new DAG nodes, or dependency repairs were needed.

Validation: `scompile.py NI lem-sfb-ordered-join-prefix-telescope` compiled the
final file in sandbox and library module mode on the server, with no errors or
warnings (15.0 s and 2.7 s respectively). An initial compile identified unused
color binder names in the helper signatures; these were renamed `_i` and the
complete final module was recompiled cleanly. `autoImplicit false` enforces
explicitly bound variables and universes. The node copy differs only in `lean`,
and its stored main signature is extracted verbatim from the delivered file.

## Second reading by NI

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
