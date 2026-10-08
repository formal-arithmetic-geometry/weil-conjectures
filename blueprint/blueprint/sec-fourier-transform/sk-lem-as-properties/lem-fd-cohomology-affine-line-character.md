+++
id = "lem-fd-cohomology-affine-line-character"
kind = "lemma"
title = "Cohomology of an affine line with an exponential sheaf"
order = 2686
uses = ["lem-fd-affine-line-constant-cohomology", "lem-fd-as-characters", "lem-fd-as-cover-affine-line", "lem-fd-as-lisse", "lem-fd-finite-pushforward-cohomology"]
+++
Let $k$ be finite or algebraically closed, let $a\in k$, and let $\psi_a(x)=\psi(ax)$. Over $\mathbf A^1_k$,

$$
H^q(\mathbf A^1_{\bar k},\mathcal L_{\psi_a})=\begin{cases}\overline{\mathbf Q}_\ell,&q=0,\ a=0,\\0,&\text{otherwise.}\end{cases}
$$

## Proof

The covering $\pi:\mathbf A^1_y\to\mathbf A^1_x$, $x=y^p-y$, of [lem-fd-as-cover-affine-line] is finite, so by [lem-fd-finite-pushforward-cohomology] and the isotypic decomposition of [lem-fd-as-characters],

$$
\bigoplus_{\chi\in\widehat{\mathbf F}_p}H^q(\mathbf A^1_x,\mathcal L_\chi)\cong H^q(\mathbf A^1_x,\pi_*\overline{\mathbf Q}_\ell)\cong H^q(\mathbf A^1_y,\overline{\mathbf Q}_\ell),
$$

which is $\overline{\mathbf Q}_\ell$ in degree $0$ and $0$ above by [lem-fd-affine-line-constant-cohomology]. The $\mathbf F_p$-action of [lem-fd-as-cover-affine-line], $y\mapsto y+a$, acts trivially on $H^0(\mathbf A^1_y,\overline{\mathbf Q}_\ell)$ (the automorphism pulls back the constant sheaf to itself), so in degree $0$ only the component $\chi=0$ survives, and the component $\chi=0$ is the constant sheaf (the deck-invariant subsheaf of $\pi_*\overline{\mathbf Q}_\ell$). Here $\mathcal L_{\psi_a}=\mathcal L_{\psi(ax)}=\mathcal L_{\psi,ax}$. For $a\neq0$ the automorphism $m_a:x\mapsto ax$ of the line satisfies $m_a^*\mathcal L_{\psi,x}=\mathcal L_{\psi,ax}$ (the Artin–Schreier covering of $ax$ is the pullback of that of $x$), so $H^q(\mathbf A^1,\mathcal L_{\psi_a})\cong H^q(\mathbf A^1,\mathcal L_{\psi,x})$; and $\mathcal L_{\psi,x}$ is the component $\mathcal L_\chi$ with $\chi=\Psi\neq0$ of the decomposition above for $f=x$ ([lem-fd-as-characters], [lem-fd-as-lisse]), so all its cohomology vanishes. For $a=0$, $\mathcal L_{\psi,0}$ is the constant sheaf (the covering is the trivial torsor) and [lem-fd-affine-line-constant-cohomology] gives $\overline{\mathbf Q}_\ell$ in degree $0$ and $0$ above.
