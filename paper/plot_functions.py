from pathlib import Path
ROOT=Path(__file__).resolve().parent
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
x=np.linspace(0,np.pi,600)
plt.rcParams.update({'pdf.fonttype':42,'ps.fonttype':42,'font.family':'DejaVu Serif','font.size':10,'axes.spines.top':False,'axes.spines.right':False})
fig,ax=plt.subplots(1,2,figsize=(8.7,2.8),constrained_layout=True)
a=(1-np.cos(x))/2;b=-(1+np.cos(x))/2;w=np.sin(x)/2
ax[0].plot(x,w,color='#135b78',lw=2,label=r'$\Omega_{\theta\phi}=\frac12\sin\theta$')
ax[0].fill_between(x,0,w,color='#135b78',alpha=.14)
ax[0].text(np.pi/2,.17,r'$\int_0^\pi \Omega_{\theta\phi}\,d\theta=1$',ha='center')
ax[0].set_ylim(0,.59);ax[0].set_title('(a) Curvature density',loc='left',fontsize=10)
ax[1].plot(x,a,color='#135b78',lw=2,label=r'$a_N$')
ax[1].plot(x,b,color='#b46b20',lw=2,label=r'$a_S$')
ax[1].plot(x,a-b,color='#444444',ls='--',lw=1.2,label=r'$a_N-a_S=1$')
ax[1].set_title('(b) Local gauge coefficients',loc='left',fontsize=10)
ax[1].set_ylim(-1.12,1.18);ax[1].legend(frameon=False,ncol=3,loc='upper center',bbox_to_anchor=(.5,-.24),fontsize=8)
for a in ax:
 a.set_xticks([0,np.pi/2,np.pi],['0',r'$\pi/2$',r'$\pi$']);a.set_xlim(0,np.pi);a.set_xlabel(r'$\theta$');a.grid(alpha=.15)
fig.savefig(ROOT/'figures/curvature_and_gauges.pdf',bbox_inches='tight')
fig.savefig(ROOT/'figures/curvature_and_gauges.png',dpi=180,bbox_inches='tight')
