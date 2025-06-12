# 1. 更新版本号（在 setup.py 中）
# 2. 清理并构建
source venv/bin/activate
# pip install --upgrade pip setuptools wheel twine
rm -rf build/ dist/ *.egg-info/
python setup.py sdist bdist_wheel

# 3. 检查包
twine check dist/*

# 4. 上传到 PyPI (注意更新版本号)
# or python setup.py upload
twine upload dist/*